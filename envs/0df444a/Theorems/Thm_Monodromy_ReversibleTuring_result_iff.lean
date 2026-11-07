-- Prove2me | Theorems.Thm_Monodromy_ReversibleTuring_result_iff
-- name    : Monodromy.ReversibleTuring.result_iff
-- status  : Proved
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:52:41.960653+00:00
-- url     : https://prove2.me/theorems/4a4cc092-c3c2-4224-b140-01aca76d10da
-- title:
--   Recorded Evaluation Preserves Complete Turing Results up to Final History
-- statement:
--   For positive naturals a,q, every Turing machine m over Fin a and Fin q, configurations x,y and natural history h, the following are equivalent: there exists a natural final history h′ such that the reversible recording table’s partial evaluation from encode(x,h) returns encode(y,h′); and the source Turing evaluation from x returns the complete halted configuration y. The existential history lies inside the recorded-result side of the equivalence; no final-history inequality is asserted.
--
--   Statement dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.eval`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.table`.
--
--   Original proof dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.eval`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.Related`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.encode_injective`, `Monodromy.ReversibleTuring.respects`, `Monodromy.ReversibleTuring.table`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.eval`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.table`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Compression.size`, `Monodromy.Counter.Reversible.Recording.edges`, `Monodromy.Counter.Reversible.Recording.size`, `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.eval`, `Monodromy.Counter.Reversible.step`, `Monodromy.Counter.TuringCompiler.size`, `Monodromy.NativeTuring.source2`, `Monodromy.NativeTuring.source3`, `Monodromy.RecordedTuring.size`, `Monodromy.ReversibleTuring.Related`, `Monodromy.ReversibleTuring.encode`, `Monodromy.ReversibleTuring.encode_injective`, `Monodromy.ReversibleTuring.respects`, `Monodromy.ReversibleTuring.table`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleTuring.result_iff at L989-L1006 [UTF-8 51323:52476].

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
open Monodromy.ReversibleTuring
open Turing
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem Monodromy.ReversibleTuring.result_iff (machine : TM0.Machine (Fin a) (Fin q))
    (first last : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    (∃ finalHistory, encode a q machine last finalHistory ∈
      Counter.Reversible.eval (table a q machine) (encode a q machine first history)) ↔
      last ∈ StateTransition.eval (TM0.step machine) first := by sorry
