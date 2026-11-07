-- Prove2me | Theorems.Thm_Monodromy_ReversibleNativeTuring_macroStep_iota
-- name    : Monodromy.ReversibleNativeTuring.macroStep_iota
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:54:15.722+00:00
-- url     : https://prove2.me/theorems/01b42c1d-21c2-48c5-ab5e-1e7dcfa9b980
-- title:
--   The Native Macro Matches Both Halted and Live Optional Source Steps
-- statement:
--   For positive naturals a,q, every Turing machine m over Fin a and Fin q, complete configuration x and natural history h, there exists a natural h′ such that the native macro at I(x,h) equals the defined partial optional source step with each successful successor y replaced by I(y,h′). If the source step is present then h<h′. In the halted case the value is defined none, and the statement imposes no condition on h′, including no equality h′=h.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.macroStep`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.ReversibleCompilation.nativeMacro_of_halt`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.macroStep`, `Monodromy.ReversibleNativeTuring.reverseMacro`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleNativeTuring.step_halt`, `Monodromy.ReversibleNativeTuring.step_return_pair`, `Monodromy.ReversibleTuring.Compression.deterministic`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.mark`, `Monodromy.ReversibleTuring.Compression.size`, `Monodromy.ReversibleTuring.Compression.table`, `Monodromy.ReversibleTuring.Compression.targetCompatible`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.macroStep`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.ReversibleCompilation.nativeMacro_of_halt`, `Monodromy.ReversibleNativeTuring.FirstReturn`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.macroStep`, `Monodromy.ReversibleNativeTuring.reverseMacro`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleNativeTuring.step_halt`, `Monodromy.ReversibleNativeTuring.step_return_pair`, `Monodromy.ReversibleTuring.Compression.deterministic`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.mark`, `Monodromy.ReversibleTuring.Compression.size`, `Monodromy.ReversibleTuring.Compression.table`, `Monodromy.ReversibleTuring.Compression.targetCompatible`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleNativeTuring.macroStep_iota at L1557-L1574 [UTF-8 83810:84915].

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

theorem Monodromy.ReversibleNativeTuring.macroStep_iota (machine : TM0.Machine (Fin a) (Fin q))
    (state : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    ∃ finalHistory,
      Monodromy.ReversibleNativeTuring.macroStep a q machine (iota a q machine state history) =
        Part.some ((TM0.step machine state).map (fun next => iota a q machine next finalHistory)) ∧
      (TM0.step machine state ≠ none → history < finalHistory) := by sorry
