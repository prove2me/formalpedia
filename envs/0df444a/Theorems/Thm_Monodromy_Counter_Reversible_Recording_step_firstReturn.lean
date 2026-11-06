-- Prove2me | Theorems.Thm_Monodromy_Counter_Reversible_Recording_step_firstReturn
-- name    : Monodromy.Counter.Reversible.Recording.step_firstReturn
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:51:05.354363+00:00
-- url     : https://prove2.me/theorems/54f3dd25-53b5-4ef9-9258-e4027b723e47
-- title:
--   A recorded source step has a first return with its transition tag
-- statement:
--   For any natural n,m, n-counter program P, successful source transition u→v and natural history h, the reversible recording table has a first return from encode(u,h) to encode(v,(2m+1)h+2·u.pc+β+1). Here β is 1 exactly for a decrement taking its nonzero branch and is 0 otherwise. Both endpoints are recording dispatches, and the positive run has no intermediate dispatch departure state.
--
--   Statement dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.Recorded.push`, `Monodromy.Counter.Recorded.tag`, `Monodromy.Counter.Reversible.Recording.FirstReturn`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.step`.
--
--   Original proof dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.Recorded.branch`, `Monodromy.Counter.Recorded.push`, `Monodromy.Counter.Recorded.tag`, `Monodromy.Counter.Reversible.Recording.FirstReturn`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.digit`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.Reversible.Recording.history_digit`, `Monodromy.Counter.Reversible.Recording.inc_firstReturn`, `Monodromy.Counter.Reversible.Recording.positive_firstReturn`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.zero_firstReturn`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.step`, `Monodromy.Counter.step_dec_succ`, `Monodromy.Counter.step_dec_zero`, `Monodromy.Counter.step_inc`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Program`, `Monodromy.Counter.Recorded.push`, `Monodromy.Counter.Recorded.tag`, `Monodromy.Counter.Reversible.Recording.FirstReturn`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.step`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Configuration`, `Monodromy.Counter.Instruction`, `Monodromy.Counter.Program`, `Monodromy.Counter.Recorded.branch`, `Monodromy.Counter.Recorded.push`, `Monodromy.Counter.Recorded.tag`, `Monodromy.Counter.Reversible.Recording.FirstReturn`, `Monodromy.Counter.Reversible.Recording.base`, `Monodromy.Counter.Reversible.Recording.digit`, `Monodromy.Counter.Reversible.Recording.encode`, `Monodromy.Counter.Reversible.Recording.history_digit`, `Monodromy.Counter.Reversible.Recording.inc_firstReturn`, `Monodromy.Counter.Reversible.Recording.positive_firstReturn`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.Recording.zero_firstReturn`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.step`, `Monodromy.Counter.step_dec_succ`, `Monodromy.Counter.step_dec_zero`, `Monodromy.Counter.step_inc`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/Counter.lean (file SHA-256 40536289575067aae1ed4154805e219805a1c786ccfdfcbe632ea7478a40636a):
--   Monodromy.Counter.Reversible.Recording.step_firstReturn at L6449-L6477 [UTF-8 323586:325394].

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

theorem Monodromy.Counter.Reversible.Recording.step_firstReturn (program : Counter.Program n m) {before after : Counter.Configuration n m}
    (transition : Counter.step program before = some after) (history : ℕ) :
    FirstReturn program (encode before history)
      (encode after (Counter.Recorded.push (Counter.Recorded.tag program before) history)) := by sorry
