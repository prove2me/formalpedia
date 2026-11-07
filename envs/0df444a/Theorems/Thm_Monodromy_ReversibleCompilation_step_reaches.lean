-- Prove2me | Theorems.Thm_Monodromy_ReversibleCompilation_step_reaches
-- name    : Monodromy.ReversibleCompilation.step_reaches
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:46:55.964438+00:00
-- url     : https://prove2.me/theorems/8de3e315-aabe-4855-9b2e-19139c08b552
-- title:
--   A reversible counter step has a positive stopped native run
-- statement:
--   For positive q and arbitrary e, let T be a two-integer-counter table whose distinct edges sharing a source or a target have complementary tests of the same register. Every successful T step from s to t yields a positive finite run of actual optional steps in its compiled halting native program from the eleven-phase encoding of s to that of t. Register values may be arbitrary integers, and no global completeness hypothesis is imposed.
--
--   Statement dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.ReversibleCompilation.haltingProgram`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleCompilation.iota`.
--
--   Original proof dependencies: `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.ReversibleCompilation.cycle_step`, `Monodromy.ReversibleCompilation.haltMark`, `Monodromy.ReversibleCompilation.haltMark_source`, `Monodromy.ReversibleCompilation.haltingProgram`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleCompilation.iota`, `Monodromy.ReversibleCompilation.sourcePoint`, `Monodromy.ReversibleCompilation.stages`, `Monodromy.StagedProgram.compile`, `Monodromy.StagedProgram.cycle_ofFn`, `Monodromy.StagedProgram.cycle_reaches`, `Monodromy.StagedProgram.embed`, `Monodromy.StagedProgram.markedCompile`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.ReversibleCompilation.haltingProgram`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleCompilation.iota`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Reversible.Action.enabled`, `Monodromy.Counter.Reversible.Deterministic`, `Monodromy.Counter.Reversible.Edge`, `Monodromy.Counter.Reversible.Edge.enabled`, `Monodromy.Counter.Reversible.Edge.execute`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.StepRel`, `Monodromy.Counter.Reversible.Table`, `Monodromy.Counter.Reversible.TargetCompatible`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.Reversible.step_iff`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.ReversibleCompilation.cycle_step`, `Monodromy.ReversibleCompilation.haltMark`, `Monodromy.ReversibleCompilation.haltMark_source`, `Monodromy.ReversibleCompilation.haltingProgram`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleCompilation.iota`, `Monodromy.ReversibleCompilation.point`, `Monodromy.ReversibleCompilation.sourcePoint`, `Monodromy.ReversibleCompilation.stages`, `Monodromy.StagedProgram.compile`, `Monodromy.StagedProgram.cycle_ofFn`, `Monodromy.StagedProgram.cycle_reaches`, `Monodromy.StagedProgram.embed`, `Monodromy.StagedProgram.markedCompile`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.ReversibleCompilation.step_reaches at L3620-L3649 [UTF-8 177718:179503].

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

theorem Monodromy.ReversibleCompilation.step_reaches (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State 2 q}
    (transition : Counter.Reversible.step table first = some last) :
    StateTransition.Reaches₁ (haltingProgram table deterministic compatible).step
      (iota (e := e) first) (iota (e := e) last) := by sorry
