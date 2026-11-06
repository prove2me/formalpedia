-- Prove2me | Theorems.Thm_Monodromy_ReversibleNativeTuring_step_return_pair
-- name    : Monodromy.ReversibleNativeTuring.step_return_pair
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:54:00.944459+00:00
-- url     : https://prove2.me/theorems/a696f100-3c94-48c0-af85-ad113ad80fe4
-- title:
--   Forward and Reverse Native Macros Share One Exact History-Retaining Return
-- statement:
--   For positive naturals a,q, a Turing machine m over Fin a and Fin q, configurations x,y satisfying TM0.step(m,x)=some y, and any natural h, there exists a single natural h′>h such that I(x,h)→I(y,h′) is the specified positive native first return, the forward macro at I(x,h) is defined with optional value some I(y,h′), and the reverse macro at I(y,h′) is defined with value I(x,h). The same h′ occurs in all three conclusions.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.macroStep`, `Monodromy.ReversibleNativeTuring.reverseMacro`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.macroStep`, `Monodromy.ReversibleNativeTuring.macroStep_of_firstReturn`, `Monodromy.ReversibleNativeTuring.reverseMacro`, `Monodromy.ReversibleNativeTuring.reverseMacro_of_firstReturn`, `Monodromy.ReversibleNativeTuring.step_firstReturn`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.macroStep`, `Monodromy.ReversibleNativeTuring.reverseMacro`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.macroStep`, `Monodromy.ReversibleNativeTuring.macroStep_of_firstReturn`, `Monodromy.ReversibleNativeTuring.reverseMacro`, `Monodromy.ReversibleNativeTuring.reverseMacro_of_firstReturn`, `Monodromy.ReversibleNativeTuring.step_firstReturn`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleNativeTuring.step_return_pair at L1543-L1555 [UTF-8 82906:83808].

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
open Monodromy.ReversibleNativeTuring
open Turing CoupledContinuation ReversibleTuring
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem Monodromy.ReversibleNativeTuring.step_return_pair (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      FirstReturn a q machine (iota a q machine first history) (iota a q machine last finalHistory) ∧
      macroStep a q machine (iota a q machine first history) =
        Part.some (some (iota a q machine last finalHistory)) ∧
      reverseMacro a q machine (iota a q machine last finalHistory) =
        Part.some (iota a q machine first history) := by sorry
