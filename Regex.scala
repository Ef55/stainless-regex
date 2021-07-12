import stainless.collection._
import stainless.lang._
import stainless.annotation._
import stainless.equations._
import stainless.proof.BoundedQuantifiers._
 
object Regex {
  type Character = Char

  sealed trait Regex {

    def nullable: Boolean = this match {
      case Empty => false
      case Epsilon => true
      case Literal(_) => false
      case Disjunction(e1, e2) => e1.nullable || e2.nullable
      case Sequence(e1, e2) => e1.nullable && e2.nullable
    }

    def derive(x: Character): Regex = this match {
      case Empty => Empty
      case Epsilon => Empty
      case Literal(char) => if(char == x) Epsilon else Empty
      case Disjunction(e1, e2) => Disjunction(e1.derive(x), e2.derive(x))
      case Sequence(e1, e2) => {
        val d1 = Sequence(e1.derive(x), e2)
        if(e1.nullable) Disjunction(d1, e2.derive(x))
        else d1
      }
    }

    def derive(str: List[Character]): Regex = {
      str.foldLeft(this)((e, x) => e.derive(x))
    }

    def accepts(str: List[Character]): Boolean = {
      this.derive(str).nullable
    }

  }

  case object Empty extends Regex
  case object Epsilon extends Regex
  case class Literal(char: Character) extends Regex

  case class Disjunction(_1: Regex, _2: Regex) extends Regex
  case class Sequence(_1: Regex, _2: Regex) extends Regex
  //case class KleeneStar(e: Regex) extends Regex


  // Lemmas
  def emptyDerivesToEmpty(@induct str: List[Character]): Unit = {
  }.ensuring(_ => Empty.derive(str) == Empty)

  def literalRejectsMoreThan1Char(e: Literal, str: List[Character]): Unit = {
    require(str.length > 1)

    val Cons(x, Cons(y, tl)) = str
    assert(e.derive(x).derive(y) == Empty)
    (
      e.derive(str)                     ==:| trivial |:
      e.derive(x).derive(y).derive(tl)  ==:| trivial |:
      Empty.derive(tl)                  ==:| emptyDerivesToEmpty(tl) |:
      Empty.asInstanceOf[Regex]
    ).qed
  }.ensuring(_ => !e.accepts(str))

  def disjunctionDerivesToDisjunctionOfDerivatives(e: Disjunction, str: List[Character]): Unit = {
    decreases(str.length) // Crashes otherwise `java.lang.AssertionError: assertion failed: Cannot add already used variable dStep$1: Regex$1 to path`

    if(str.length == 0) {
      () // Trivial
    }
    else if(str.length == 1) {
      () // Trivial
    }
    else {
      val Cons(h, t) = str
      val Disjunction(e1, e2) = e
      val dStep = Disjunction(e1.derive(h), e2.derive(h))

      (
        e.derive(str)               ==:| trivial |:
        e.derive(h).derive(t)       ==:| trivial |:
        dStep.derive(t)             ==:| disjunctionDerivesToDisjunctionOfDerivatives(dStep, t) |:
        Disjunction(e1.derive(str), e2.derive(str)).asInstanceOf[Regex]
      ).qed
    }
  }.ensuring(_ => e.derive(str) == Disjunction(e._1.derive(str), e._2.derive(str)))

  def disjunctionLeftUnit(e: Regex, str: List[Character]): Unit = {
    val d = Disjunction(e, Empty)
    val dPrime = Disjunction(e.derive(str), Empty.derive(str))

    (
      d.accepts(str)                                ==:| disjunctionDerivesToDisjunctionOfDerivatives(d, str) |:
      dPrime.nullable                               ==:| emptyDerivesToEmpty(str) |:
      Disjunction(e.derive(str), Empty).nullable    ==:| trivial |:
      (e.derive(str).nullable || Empty.nullable)    ==:| trivial |:
      e.derive(str).nullable                        ==:| trivial |:
      e.accepts(str)
    ).qed
  }.ensuring(_ => Disjunction(e, Empty).accepts(str) == e.accepts(str))

  def nilAccepterIsNullable(e: Regex): Unit = {
    require(e.accepts(Nil()))
  }.ensuring(_ => e.nullable)

  def derivationChain(e: Regex, str1: List[Character], str2: List[Character]): Boolean = {
    decreases(str1.length + str2.length)

    str1 match {
      case Nil() => assert(str1 ++ str2 == str2)
      case Cons(h, t) => {
        if(t.length < 2) {
          ()
        }
        else {
          val d = e.derive(h)

          (
            e.derive(Cons(h, t)).derive(str2)         ==:| trivial |:
            d.derive(t).derive(str2)                  ==:| derivationChain(d, t, str2) |:
            d.derive(t ++ str2)                       ==:| trivial |:
            e.derive(Cons(h, (t ++ str2)))            ==:| trivial |:
            e.derive(Cons(h, t) ++ str2)              ==:| trivial |:
            e.derive(str1 ++ str2)
          ).qed
        }
      }
    }

    e.derive(str1).derive(str2) == e.derive(str1 ++ str2)
  }.holds

  def derivationChainHead(e: Regex, str1: List[Character], str2: List[Character]): Boolean = {
    require(!str1.isEmpty)
    val Cons(h, t) = str1
    (
      e.derive(str1 ++ str2)              ==:| derivationChain(e, str1, str2) |:
      e.derive(str1).derive(str2)         ==:| trivial |:
      e.derive(h).derive(t).derive(str2)  ==:| derivationChain(e.derive(h), t, str2) |:
      e.derive(h).derive(t ++ str2)
    ).qed
    e.derive(h).derive(t ++ str2) == e.derive(str1 ++ str2)
  }.holds

  // Core properties
  def emptyAccepts(@induct str: List[Character]): Unit = {
    require(Empty.accepts(str))
  }.ensuring(_ => false)

  def epsilonAccepts(@induct str: List[Character]): Unit = {
    require(Epsilon.accepts(str))
  }.ensuring(_ => str.isEmpty)

  def epsilonRejects(str: List[Character]): Unit = {
    require(!Epsilon.accepts(str))
  }.ensuring(_ => !str.isEmpty)

  def literalAccepts(e: Literal, str: List[Character]): Unit = {
    require(e.accepts(str))

    if(str.length > 1) {
      literalRejectsMoreThan1Char(e, str)
      assert(!e.accepts(str)) // Contradiction
    }
    else if(str.length == 0) {
      assert(str == Nil())
      assert(!e.accepts(Nil())) // Contradiction
    }
    else{
      assert(str.length == 1) // Trivial
    }

  }.ensuring(_ => str == Cons(e.char, Nil()))

  def literalRejects(e: Literal, str: List[Character]): Unit = {
    require(!e.accepts(str))
  }.ensuring(_ => str != Cons(e.char, Nil()))

  def disjunctionAccepts(e: Disjunction, str: List[Character]): Unit = {
    require(e.accepts(str))

    val Disjunction(e1, e2) = e
    if(!e1.accepts(str) && !e2.accepts(str)) {
      val d1 = e1.derive(str)
      val d2 = e2.derive(str)

      assert(!d1.nullable)
      assert(!d2.nullable)
      (
        (!d1.nullable && !d2.nullable)      ==:| trivial |:
        !Disjunction(d1, d2).nullable       ==:| disjunctionDerivesToDisjunctionOfDerivatives(e, str) |:
        !e.derive(str).nullable             ==:| trivial |:
        !e.accepts(str)
      ).qed // Contradiction
    }

  }.ensuring(_ => e._1.accepts(str) || e._2.accepts(str))

  def disjunctionRejects(e: Disjunction, str: List[Character]): Unit = {
    require(!e.accepts(str))

    val Disjunction(e1, e2) = e
    if(e1.accepts(str)) {
      val d1 = e1.derive(str)
      val d2 = e2.derive(str)

      assert(d1.nullable)
      (
        d1.nullable                         ==:| trivial |:
        Disjunction(d1, d2).nullable        ==:| disjunctionDerivesToDisjunctionOfDerivatives(e, str) |:
        e.derive(str).nullable              ==:| trivial |:
        e.accepts(str)
      ).qed // Contradiction
    }
    else if(e2.accepts(str)) {
      val d1 = e1.derive(str)
      val d2 = e2.derive(str)

      assert(d2.nullable)
      (
        d2.nullable                         ==:| trivial |:
        Disjunction(d1, d2).nullable        ==:| disjunctionDerivesToDisjunctionOfDerivatives(e, str) |:
        e.derive(str).nullable              ==:| trivial |:
        e.accepts(str)
      ).qed // Contradiction
    }
    else {
      ()
    }

  }.ensuring(_ => !e._1.accepts(str) && !e._2.accepts(str))

  // TODO: cleanup
  def sequenceAccepts(e: Sequence, str1: List[Character], str2: List[Character]): Unit = {
    require(e._1.accepts(str1))
    require(e._2.accepts(str2))
    val Sequence(e1, e2) = e

    str1 match {
      case Nil() => {
        if(str2.isEmpty) {
          (
            e.accepts(str1 ++ str2)           ==:| trivial |:
            e.accepts(Nil())                  ==:| trivial |:
            e.nullable                        ==:| trivial |:
            (e1.nullable && e2.nullable)      ==:| nilAccepterIsNullable(e1) |:
            (true && e2.nullable)             ==:| nilAccepterIsNullable(e2) |:
            (true && true)
          ).qed
        }
        else {
          val Cons(h, t) = str2
          val d = Disjunction(Sequence(e1.derive(h), e2), e2.derive(h))
          (
            e.derive(str1 ++ str2).nullable                                                     ==:| derivationChain(e, str1, str2) |:
            e.derive(str1).derive(str2).nullable                                                ==:| trivial |:
            e.derive(str2).nullable                                                             ==:| trivial |:
            e.derive(h).derive(t).nullable                                                      ==:| nilAccepterIsNullable(e1) |:
            d.derive(t).nullable                                                                ==:| disjunctionDerivesToDisjunctionOfDerivatives(d, t) |:
            Disjunction(Sequence(e1.derive(h), e2).derive(t), e2.derive(h).derive(t)).nullable  ==:| trivial |:
            Disjunction(Sequence(e1.derive(h), e2).derive(t), e2.derive(str2)).nullable         ==:| trivial |:
            (Sequence(e1.derive(h), e2).derive(t).nullable || e2.derive(str2).nullable)         ==:| trivial |:
            (Sequence(e1.derive(h), e2).derive(t).nullable || true)
          ).qed
        }
      }

      case Cons(h, t) => {
        if(e1.nullable) {
          val d1 = Disjunction(Sequence(e1.derive(h), e2), e2.derive(h))
          val s = Sequence(e1.derive(h), e2)
          (
            e.accepts(str1 ++ str2)                                       ==:| trivial |:
            e.derive(str1 ++ str2).nullable                               ==:| derivationChainHead(e, str1, str2) |:
            e.derive(h).derive(t ++ str2).nullable                        ==:| trivial |:
            d1.derive(t ++ str2).nullable                                 ==:| disjunctionDerivesToDisjunctionOfDerivatives(d1, t ++ str2) |:
            Disjunction(s.derive(t ++ str2), 
              e2.derive(h).derive(t ++ str2)).nullable                    ==:| trivial |:
            ( s.derive(t ++ str2).nullable || 
              e2.derive(h).derive(t ++ str2).nullable )                   ==:| sequenceAccepts(s, t, str2) |:
            ( true || e2.derive(h).derive(t ++ str2).nullable )
          ).qed
          
        }
        else {
          val d = Sequence(e1.derive(h), e2)
          (
            e.accepts(str1 ++ str2)                                     ==:| derivationChainHead(e, str1, str2) |:
            e.derive(h).derive(t ++ str2).nullable                      ==:| trivial |:
            d.derive(t ++ str2).nullable                                ==:| sequenceAccepts(d, t, str2) |:
            true
          ).qed
        }
      }
    }
    
  }.ensuring(_ => 
    e.accepts(str1 ++ str2)
  )

  def sequenceRejects(e1: Regex, e2: Regex, str: List[Character]): Unit = {
    require(false)
  }.ensuring(_ => !Sequence(e1, e2).accepts(str))


  // Additional properties
  def disjunctionSymmetry(e1: Regex, e2: Regex, str: List[Character]): Unit = {
    val d1 = Disjunction(e1, e2)
    val d2 = Disjunction(e2, e1)

    if(d1.accepts(str)) {
      (
        d1.accepts(str)                         ==:| disjunctionDerivesToDisjunctionOfDerivatives(d1, str) |:
        (e1.accepts(str) || e2.accepts(str))    ==:| disjunctionDerivesToDisjunctionOfDerivatives(d2, str) |:
        d2.accepts(str)
      ).qed
    }
    else {
      (
        !d1.accepts(str)                        ==:| disjunctionDerivesToDisjunctionOfDerivatives(d1, str) |:
        (!e1.accepts(str) && !e2.accepts(str))  ==:| disjunctionDerivesToDisjunctionOfDerivatives(d2, str) |:
        !d2.accepts(str)
      ).qed
    }

  }.ensuring(_ => Disjunction(e1, e2).accepts(str) == Disjunction(e2, e1).accepts(str))

  def disjunctionUnit(e: Regex, str: List[Character]): Unit = {
    disjunctionLeftUnit(e, str)
    disjunctionSymmetry(e, Empty, str)
  }.ensuring(_ => 
    (Disjunction(e, Empty).accepts(str) == e.accepts(str)) &&
    (Disjunction(Empty, e).accepts(str) == e.accepts(str))
  )

  def disjunctionAssociativity(e1: Regex, e2: Regex, e3: Regex, str: List[Character]): Unit = {
    val d1 = Disjunction(e1, e2)
    val d2 = Disjunction(e2, e3)
    disjunctionDerivesToDisjunctionOfDerivatives(d1, str)
    disjunctionDerivesToDisjunctionOfDerivatives(d2, str)
    disjunctionDerivesToDisjunctionOfDerivatives(Disjunction(e1, d2), str)
    disjunctionDerivesToDisjunctionOfDerivatives(Disjunction(d1, e3), str)
  }.ensuring(_ => 
    Disjunction(Disjunction(e1, e2), e3).accepts(str) ==
    Disjunction(e1, Disjunction(e2, e3)).accepts(str)
  )

  def disjunctionIdempotence(e: Regex, str: List[Character]): Unit = {
    val d = Disjunction(e, e)
    disjunctionDerivesToDisjunctionOfDerivatives(d, str)
  }.ensuring(_ => Disjunction(e, e).accepts(str) == e.accepts(str))
  
}