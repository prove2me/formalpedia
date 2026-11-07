-- Prove2me | Theorems.Thm_Monodromy_CounterContinuation_two_returns_with_boundary
-- name    : Monodromy.CounterContinuation.two_returns_with_boundary
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:46:26.580357+00:00
-- url     : https://prove2.me/theorems/ff1a35fd-b6f2-46e2-8f80-d32ccbecadde
-- title:
--   Consecutive source boundaries are separated by two native steps
-- statement:
--   For every positive m and two-counter program P, each successful source step s→t admits a native state u such that encode(s) is a source boundary, the compiled optional steps are encode(s)→u→encode(t), u is not a source boundary, and encode(t) is a source boundary. A source boundary means that the cubic control-root observation equals 1.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.SourceBoundary`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.SourceBoundary`, `Monodromy.CounterContinuation.advance_live_not_boundary`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.instructionStop`, `Monodromy.CounterContinuation.sourceBoundary_encode`, `Monodromy.CounterContinuation.step_running_at`, `Monodromy.CounterContinuation.stopping`, `Monodromy.CounterContinuation.two_returns`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.step`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.SourceBoundary`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.SourceBoundary`, `Monodromy.CounterContinuation.advance_live_not_boundary`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.instructionStop`, `Monodromy.CounterContinuation.sourceBoundary_encode`, `Monodromy.CounterContinuation.step_running_at`, `Monodromy.CounterContinuation.stopping`, `Monodromy.CounterContinuation.two_returns`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.CounterContinuation.two_returns_with_boundary at L568-L590 [UTF-8 25902:27249].

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
open Monodromy.CounterContinuation
open CoupledContinuation
variable {m : ℕ} [NeZero m]

theorem Monodromy.CounterContinuation.two_returns_with_boundary (program : Counter.Program 2 m)
    (state result : Counter.Configuration 2 m) (source_step : Counter.step program state = some result) :
    ∃ middle : Memory,
      SourceBoundary (encode state) ∧
      (compile program).step (encode state) = some middle ∧
      ¬ SourceBoundary middle ∧
      (compile program).step middle = some (encode result) ∧
      SourceBoundary (encode result) := by sorry
