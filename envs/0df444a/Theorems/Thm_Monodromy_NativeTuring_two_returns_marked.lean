-- Prove2me | Theorems.Thm_Monodromy_NativeTuring_two_returns_marked
-- name    : Monodromy.NativeTuring.two_returns_marked
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:46:41.909316+00:00
-- url     : https://prove2.me/theorems/3e12ee62-9316-43dc-831b-5dcf892c98b3
-- title:
--   A Compiled Counter Step Has an Unmarked Intermediate Native Return
-- statement:
--   For every positive number m of counter addresses, two-counter program C with m addresses, Boolean mark table b:Fin m→Bool and configurations x,y with C.step(x)=some y, there exists a native state u such that the compiled program steps from encode(x) to u, u fails the finite phase-zero boundary observation selected by b, and the next compiled step returns encode(y). The mark table is arbitrary.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.NativeTuring.MarkedBoundary`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.advance_live_phase`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.label`, `Monodromy.CounterContinuation.two_returns`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.NativeTuring.MarkedBoundary`, `Monodromy.NativeTuring.advance_of_native_step`, `Monodromy.NativeTuring.markedBoundary_label_iff`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.NativeTuring.MarkedBoundary`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.step`, `Monodromy.CounterContinuation.advance_live_phase`, `Monodromy.CounterContinuation.compile`, `Monodromy.CounterContinuation.encode`, `Monodromy.CounterContinuation.label`, `Monodromy.CounterContinuation.two_returns`, `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.advance`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.CoupledContinuation.prepare`, `Monodromy.NativeTuring.MarkedBoundary`, `Monodromy.NativeTuring.advance_of_native_step`, `Monodromy.NativeTuring.markedBoundary_label_iff`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.NativeTuring.two_returns_marked at L463-L481 [UTF-8 22263:23311].

module
public import Definitions.Def_Monodromy_FormalCompilation
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
public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sets
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
open Monodromy.NativeTuring
open Turing CoupledContinuation
variable {m : ℕ} [NeZero m]

theorem Monodromy.NativeTuring.two_returns_marked (source : Counter.Program 2 m) (mark : Fin m → Bool)
    (first last : Counter.Configuration 2 m) (transition : Counter.step source first = some last) :
    ∃ middle : Memory,
      (CounterContinuation.compile source).step (CounterContinuation.encode first) = some middle ∧
      ¬ MarkedBoundary source mark middle ∧
      (CounterContinuation.compile source).step middle = some (CounterContinuation.encode last) := by sorry
