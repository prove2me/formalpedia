-- Prove2me | Theorems.Thm_Monodromy_ReversibleNativeTuring_result_iff
-- name    : Monodromy.ReversibleNativeTuring.result_iff
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:53:46.766206+00:00
-- url     : https://prove2.me/theorems/bf2fcba1-08f3-4c66-9ef1-5d0c40180413
-- title:
--   Native Partial Evaluation Retains Exactly the Complete Source Results
-- statement:
--   For positive naturals a,q, every Turing machine m over Fin a and Fin q, complete configurations x,y and natural history h, the existential statement that P.eval(I(x,h)) returns I(y,h′) for some natural h′ is equivalent to the source Turing evaluation from x returning y. Here P and I are the specified reversible native compiler and its configuration-history encoding. No inequality between initial and terminal histories is asserted.
--
--   Statement dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
--
--   Original proof dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.Related`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.iota_injective`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.respects`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
--
--   Statement elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
--
--   Proof elaboration dependencies: `Monodromy.CoupledContinuation.Memory`, `Monodromy.CoupledContinuation.Point`, `Monodromy.CoupledContinuation.Program.eval`, `Monodromy.CoupledContinuation.Program.step`, `Monodromy.ReversibleCompilation.instNeZeroNatHAdd_monodromy`, `Monodromy.ReversibleNativeTuring.Related`, `Monodromy.ReversibleNativeTuring.iota`, `Monodromy.ReversibleNativeTuring.iota_injective`, `Monodromy.ReversibleNativeTuring.program`, `Monodromy.ReversibleNativeTuring.respects`, `Monodromy.ReversibleNativeTuring.size_nonzero`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.size`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleNativeTuring.result_iff at L1445-L1462 [UTF-8 76644:77787].

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

theorem Monodromy.ReversibleNativeTuring.result_iff (machine : TM0.Machine (Fin a) (Fin q))
    (first last : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    (∃ finalHistory, iota a q machine last finalHistory ∈
      (program a q machine).eval (iota a q machine first history)) ↔
      last ∈ StateTransition.eval (TM0.step machine) first := by sorry
