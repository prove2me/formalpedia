-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_PrimeCompression_step_firstReturn
-- name    : Monodromy.Counter.Reversible.PrimeCompression.step_firstReturn
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:50:50.151219+00:00
-- url     : https://prove2.me/theorems/d93e48f4-bc43-4ac3-990f-5c8d5593d616
-- title:
--   Unit-shift source transitions survive prime compression as first returns
-- statement:
--   For arbitrary natural n,q,e, distinct-prime basis and source table with complementary same-register tests at shared source or target vertices, assume every shift amount is either +1 or −1; tests are also allowed. Every successful source step between the integer casts of two natural-counter configurations u,v yields a first return between their two-counter prime encodings. Both endpoints are retained source boundaries, and one successful compiled step is followed by a finite possibly empty chain whose departure states avoid those boundaries.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Action.UnitShift`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.PrimeCompression.FirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.naturalState`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.PrimeCode.Basis`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.UnitShift`, `Monodromy.Counter.Reversible.Action.apply`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.PrimeCompression.FirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.decrement_firstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.increment_firstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.naturalState`, `Monodromy.Counter.Reversible.PrimeCompression.naturalState_injective`, `Monodromy.Counter.Reversible.PrimeCompression.naturalState_shift`, `Monodromy.Counter.Reversible.PrimeCompression.test_firstReturn`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`, `Monodromy.PrimeCode.Basis`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Action.UnitShift`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.PrimeCompression.FirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.naturalState`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.PrimeCode.Basis`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Reversible.Action`, `Monodromy.Counter.Reversible.Action.UnitShift`, `Monodromy.Counter.Reversible.Action.apply`, `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.PrimeCompression.FirstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.decrement_firstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.increment_firstReturn`, `Monodromy.Counter.Reversible.PrimeCompression.naturalState`, `Monodromy.Counter.Reversible.PrimeCompression.naturalState_injective`, `Monodromy.Counter.Reversible.PrimeCompression.naturalState_shift`, `Monodromy.Counter.Reversible.PrimeCompression.test_firstReturn`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`, `Monodromy.PrimeCode.Basis`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.PrimeCompression.step_firstReturn at L8181-L8231 [UTF-8 425855:428840].

module
public import Definitions.Def_Monodromy_Counter
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
public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homotopy.Lifting

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.PrimeCompression
variable {n q e : ℕ}

theorem Monodromy.Counter.Reversible.PrimeCompression.step_firstReturn (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action)
    {before after : Counter.Configuration n q}
    (transition : step source (naturalState before) = some (naturalState after)) :
    FirstReturn basis source deterministic compatible
      (encode basis source deterministic compatible before)
      (encode basis source deterministic compatible after) := by sorry
