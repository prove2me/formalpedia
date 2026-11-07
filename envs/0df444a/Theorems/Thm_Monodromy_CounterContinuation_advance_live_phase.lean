-- Prove2me | Theorems.Thm_Monodromy_CounterContinuation_advance_live_phase
-- name    : Monodromy.CounterContinuation.advance_live_phase
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:41:49.156211+00:00
-- url     : https://prove2.me/theorems/b49feb6e-83c6-42ab-8bd9-4d9fc45508c7
-- title:
--   A live configuration advances to a nonzero phase
-- statement:
--   For every positive m, two-counter program P with m addresses, and configuration s whose instruction is not halt, the total native advance from encode(s) is one of prepare(s.counter₀,s.counter₁,3·s.pc+1) and prepare(s.counter₀,s.counter₁,3·s.pc+2). This disjunction preserves both source counter values and does not choose between the two phases.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.label`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.prepare`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.CounterContinuation.advance_dec_first`, `Monodromy.CounterContinuation.advance_inc_first`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.label`, `Monodromy.CounterContinuation.label_eq`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.prepare`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.label`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.prepare`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.CounterContinuation.advance_dec_first`, `Monodromy.CounterContinuation.advance_inc_first`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.label`, `Monodromy.CounterContinuation.label_eq`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.prepare`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.CounterContinuation.advance_live_phase at L536-L557 [UTF-8 24404:25510].

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

theorem Monodromy.CounterContinuation.advance_live_phase (program : Counter.Program 2 m) (state : Counter.Configuration 2 m)
    (live : program state.pc ≠ .halt) :
    (compile program).advance (encode state) =
      prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 1) ∨
    (compile program).advance (encode state) =
      prepare (state.counters 0 : ℤ) (state.counters 1 : ℤ) (label state.pc 2) := by sorry
