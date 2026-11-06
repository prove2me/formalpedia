-- Prove2me | Theorems.Thm_Monodromy_ReversibleReturn_inverse_firstReturn
-- name    : Monodromy.ReversibleReturn.inverse_firstReturn
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:38:04.34786+00:00
-- url     : https://prove2.me/theorems/645320cf-a36e-4266-b7eb-2b77b6953679
-- title:
--   A Left Inverse Retraces a Positive First Return
-- statement:
--   For any type S, maps A,R:S→S and predicate B:S→Prop, assume R(A(s))=s for every s. If s→t is a positive first return under A to B—both endpoints lie in B and no earlier positive iterate does—then t→s is a positive first return under R to the same predicate B. A right-inverse premise is not assumed.
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
--   Monodromy.ReversibleReturn.inverse_firstReturn at L3145-L3163 [UTF-8 158149:159300].

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

theorem Monodromy.ReversibleReturn.inverse_firstReturn {advance backward : State → State} {boundary : State → Prop}
    (inverse : Function.LeftInverse backward advance) {first last : State}
    (run : FirstReturn advance boundary first last) :
    FirstReturn backward boundary last first := by sorry
