-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_PrimeCompression_integer_internal_reaches
-- name    : Monodromy.Counter.Reversible.PrimeCompression.integer_internal_reaches
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:51:20.483658+00:00
-- url     : https://prove2.me/theorems/76e592b0-ccd3-402f-b2ad-244cc87807a9
-- title:
--   Stable nonnegative unmarked runs lift through prime compression
-- statement:
--   For arbitrary natural n,q,e, distinct-prime basis, source table with complementary same-register tests at shared sources and targets, and shift amounts restricted to ±1, choose a Boolean source-address marking and an invariant preserved by every successful source step. Suppose the invariant makes every register nonnegative. Any finite possibly empty integer source run from an invariant-satisfying state u to v, with a false mark at every departure address, induces a finite compressed-table run between the prime encodings of the configurations obtained by applying Int.toNat to their counters. Every compressed departure state avoids the marked retained source boundaries; no marking or halting assumption is imposed on v.
--
--   Statement dependencies: `Monodromy.Counter.Reversible.Action.UnitShift`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedReaches`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.toNatural`, `Monodromy.Counter.Reversible.Stable`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.PrimeCode.Basis`.
--
--   Original proof dependencies: `Monodromy.Counter.Reversible.Action.UnitShift`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedReaches`, `Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedStep`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.integer_unmarked_step`, `Monodromy.Counter.Reversible.PrimeCompression.size`, `Monodromy.Counter.Reversible.PrimeCompression.toNatural`, `Monodromy.Counter.Reversible.Stable`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.PrimeCode.Basis`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Reversible.Action.UnitShift`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedReaches`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.toNatural`, `Monodromy.Counter.Reversible.Stable`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.PrimeCode.Basis`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Reversible.Action.UnitShift`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedReaches`, `Monodromy.Counter.Reversible.PrimeCompression.InternalMarkedStep`, `Monodromy.Counter.Reversible.PrimeCompression.encode`, `Monodromy.Counter.Reversible.PrimeCompression.integer_unmarked_step`, `Monodromy.Counter.Reversible.PrimeCompression.size`, `Monodromy.Counter.Reversible.PrimeCompression.toNatural`, `Monodromy.Counter.Reversible.Stable`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.PrimeCode.Basis`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.PrimeCompression.integer_internal_reaches at L8385-L8408 [UTF-8 438350:439891].

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

theorem Monodromy.Counter.Reversible.PrimeCompression.integer_internal_reaches (basis : PrimeCode.Basis n) (source : Table n q e)
    (deterministic : Deterministic source) (compatible : TargetCompatible source)
    (unit : ∀ edge, Action.UnitShift (source edge).action) (mark : Fin q → Bool)
    (valid : State n q → Prop) (stable : Stable source valid)
    (nonnegative : ∀ state, valid state → ∀ index, 0 ≤ state.2 index)
    {first last : State n q}
    (run : Relation.ReflTransGen (fun current next : State n q =>
      step source current = some next ∧ mark current.1 = false) first last)
    (first_valid : valid first) :
    InternalMarkedReaches basis source deterministic compatible mark
      (encode basis source deterministic compatible (toNatural first))
      (encode basis source deterministic compatible (toNatural last)) := by sorry
