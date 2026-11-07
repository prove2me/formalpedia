-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Recording_counter_internal_reaches
-- name    : Monodromy.Counter.Reversible.Recording.counter_internal_reaches
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:51:33.969021+00:00
-- url     : https://prove2.me/theorems/287c49dd-5152-4a1e-972b-1bd46ebbba40
-- title:
--   An unmarked counter run lifts with nondecreasing history
-- statement:
--   For arbitrary natural n,m, n-counter program P and Boolean marking of its addresses, suppose a finite possibly empty source run u→*v consists of successful source steps with a false mark at every departure configuration. For every initial natural history h, there is a final natural history H≥h and a finite recording-table run from encode(u,h) to encode(v,H) whose departure states avoid all marked recording dispatches. The final source configuration need not be unmarked or halted.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Recording.InternalMarkedReaches`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.Recorded.State`, `Monodromy.Counter.Recorded.history_lt`, `Monodromy.Counter.Recorded.push`, `Monodromy.Counter.Recorded.step`, `Monodromy.Counter.Recorded.tag`, `Monodromy.Counter.Reversible.Recording.InternalMarkedReaches`, `Monodromy.Counter.Reversible.Recording.InternalMarkedStep`, `Monodromy.Counter.Reversible.Recording.counter_internal_step`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.step`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.Reversible.Recording.InternalMarkedReaches`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.Recorded.State`, `Monodromy.Counter.Recorded.history_lt`, `Monodromy.Counter.Recorded.push`, `Monodromy.Counter.Recorded.step`, `Monodromy.Counter.Recorded.tag`, `Monodromy.Counter.Reversible.Recording.InternalMarkedReaches`, `Monodromy.Counter.Reversible.Recording.InternalMarkedStep`, `Monodromy.Counter.Reversible.Recording.counter_internal_step`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.step`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Recording.counter_internal_reaches at L6579-L6597 [UTF-8 330866:332137].

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
open Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}

theorem Monodromy.Counter.Reversible.Recording.counter_internal_reaches (program : Counter.Program n m) (mark : Fin m → Bool)
    {first last : Counter.Configuration n m}
    (run : Relation.ReflTransGen (fun current next : Counter.Configuration n m =>
      Counter.step program current = some next ∧ mark current.pc = false) first last)
    (history : ℕ) :
    ∃ finalHistory, history ≤ finalHistory ∧
      InternalMarkedReaches program mark (encode first history) (encode last finalHistory) := by sorry
