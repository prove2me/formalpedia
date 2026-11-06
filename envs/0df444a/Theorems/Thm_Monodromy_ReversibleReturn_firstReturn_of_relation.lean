-- Prove2me | Theorems.Thm_Monodromy_ReversibleReturn_firstReturn_of_relation
-- name    : Monodromy.ReversibleReturn.firstReturn_of_relation
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:37:50.555406+00:00
-- url     : https://prove2.me/theorems/fd22ecd3-a61b-4148-9f04-2a331119f56c
-- title:
--   Boundary-Avoiding Relational Runs Give Positive First Returns
-- statement:
--   For any type S, map A:S→S, predicate B:S→Prop and relation T on S, suppose every T(x,y) implies A(x)=y. If T(s,u), a finite possibly empty chain of T-edges from u reaches t while every departure state is outside B, and both s and t satisfy B, then there exists n>0 with Aⁿ(s)=t and no positive iterate Aᵏ(s) in B for 0<k<n. Thus s→t is a first return for A at B.
--
--   Statement dependencies: `Monodromy.ReversibleReturn.FirstReturn`.
--
--   Original proof dependencies: `Monodromy.ReversibleReturn.FirstReturn`.
--
--   Statement elaboration dependencies: `Monodromy.ReversibleReturn.FirstReturn`.
--
--   Proof elaboration dependencies: `Monodromy.ReversibleReturn.FirstReturn`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Continuation.lean (file SHA-256 c41996cad30503403fe284de8929124f849aa5fd0aaba5433e5e0d4d36fec912):
--   Monodromy.ReversibleReturn.firstReturn_of_relation at L3114-L3143 [UTF-8 156545:158147].

module
public import Definitions.Def_Monodromy_Continuation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.ReversibleReturn
variable {State : Type*}

theorem Monodromy.ReversibleReturn.firstReturn_of_relation {advance : State → State} {boundary : State → Prop}
    {transition : State → State → Prop}
    (executes : ∀ {left right}, transition left right → advance left = right)
    {first after last : State} (initial : transition first after)
    (interior : Relation.ReflTransGen
      (fun left right => transition left right ∧ ¬ boundary left) after last)
    (marked_first : boundary first) (marked_last : boundary last) :
    FirstReturn advance boundary first last := by sorry
