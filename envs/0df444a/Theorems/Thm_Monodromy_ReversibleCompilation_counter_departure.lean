-- Prove2me | Theorems.Thm_Monodromy_ReversibleCompilation_counter_departure
-- name    : Monodromy.ReversibleCompilation.counter_departure
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:48:17.706073+00:00
-- url     : https://prove2.me/theorems/43e42f7e-7013-411f-a7b6-a771b462178c
-- title:
--   A native counter simulation departs before its next marked return
-- statement:
--   For positive q and arbitrary e, let T be a two-integer-counter table with complementary same-register tests at shared sources and targets, and choose any Boolean marking of its source vertices. For every successful T step s→t, there is a native state u reached by one successful step of the compiled halting program from the eleven-phase encoding of s, followed by a finite possibly empty chain of that same program’s successful steps to the encoding of t whose departure states are unmarked by the native finite-root observation. There is no hypothesis that either endpoint is marked, and the source registers may be arbitrary integers.
--
--   Statement dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.ReversibleCompilation.NativeInternalReaches`, `Monodromy.ReversibleCompilation.haltingProgram`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleCompilation.iota`.
--
--   Original proof dependencies: `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.haltSignal`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.ReversibleCompilation.MarkedBoundary`, `Monodromy.ReversibleCompilation.NativeInternalReaches`, `Monodromy.ReversibleCompilation.NativeInternalStep`, `Monodromy.ReversibleCompilation.haltMark`, `Monodromy.ReversibleCompilation.haltSignal_iota_iff`, `Monodromy.ReversibleCompilation.haltingProgram`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleCompilation.iota`, `Monodromy.ReversibleCompilation.markedBoundary_phase`, `Monodromy.ReversibleCompilation.stages`, `Monodromy.ReversibleCompilation.step_firstReturn`, `Monodromy.ReversibleCompilation.stopped_phase`, `Monodromy.StagedProgram.PhaseBoundary`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.ReversibleCompilation.NativeInternalReaches`, `Monodromy.ReversibleCompilation.haltingProgram`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleCompilation.iota`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.haltSignal`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.ReversibleCompilation.MarkedBoundary`, `Monodromy.ReversibleCompilation.NativeInternalReaches`, `Monodromy.ReversibleCompilation.NativeInternalStep`, `Monodromy.ReversibleCompilation.haltMark`, `Monodromy.ReversibleCompilation.haltSignal_iota_iff`, `Monodromy.ReversibleCompilation.haltingProgram`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleCompilation.iota`, `Monodromy.ReversibleCompilation.markedBoundary_phase`, `Monodromy.ReversibleCompilation.stages`, `Monodromy.ReversibleCompilation.step_firstReturn`, `Monodromy.ReversibleCompilation.stopped_phase`, `Monodromy.StagedProgram.PhaseBoundary`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.ReversibleCompilation.counter_departure at L8517-L8557 [UTF-8 445957:448375].

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
open Monodromy.ReversibleCompilation
open Counter.Reversible CoupledContinuation
variable {q e : ℕ} [NeZero q]

theorem Monodromy.ReversibleCompilation.counter_departure (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) (mark : Fin q → Bool) {first last : State 2 q}
    (transition : Counter.Reversible.step table first = some last) :
    ∃ next, (haltingProgram table deterministic compatible).step (iota (e := e) first) = some next ∧
      NativeInternalReaches table deterministic compatible mark next (iota (e := e) last) := by sorry
