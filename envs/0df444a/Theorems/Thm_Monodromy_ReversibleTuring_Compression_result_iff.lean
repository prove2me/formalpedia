-- Prove2me | Theorems.Thm_Monodromy_ReversibleTuring_Compression_result_iff
-- name    : Monodromy.ReversibleTuring.Compression.result_iff
-- status  : Open
-- author  : @Xiaoyang Liu
-- created : 2026-11-05T18:53:13.085197+00:00
-- url     : https://prove2.me/theorems/36b678a8-0109-45f2-9262-9ddbe027ad82
-- title:
--   Prime-Compressed Evaluation Preserves Complete Turing Results
-- statement:
--   For positive naturals a,q, every Turing machine m over Fin a and Fin q, configurations x,y and natural initial history h, the following are equivalent: there exists a natural h′ for which the prime-compressed reversible table’s partial evaluation from encode(x,h) returns encode(y,h′); and the source Turing evaluation from x returns the complete halted configuration y. The existential final history is inside the compressed-result side of the equivalence; no final-history inequality is asserted.
--
--   Statement dependencies: `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.eval`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.encode`, `Monodromy.ReversibleTuring.Compression.size`, `Monodromy.ReversibleTuring.Compression.table`.
--
--   Original proof dependencies: `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.eval`, `Monodromy.Counter.Reversible.step`, `Monodromy.ReversibleTuring.Compression.Related`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.encode`, `Monodromy.ReversibleTuring.Compression.encode_injective`, `Monodromy.ReversibleTuring.Compression.respects`, `Monodromy.ReversibleTuring.Compression.size`, `Monodromy.ReversibleTuring.Compression.table`.
--
--   Statement elaboration dependencies: `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.eval`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.encode`, `Monodromy.ReversibleTuring.Compression.size`, `Monodromy.ReversibleTuring.Compression.table`.
--
--   Proof elaboration dependencies: `Monodromy.Counter.Reversible.State`, `Monodromy.Counter.Reversible.eval`, `Monodromy.Counter.Reversible.step`, `Monodromy.ReversibleTuring.Compression.Related`, `Monodromy.ReversibleTuring.Compression.edges`, `Monodromy.ReversibleTuring.Compression.encode`, `Monodromy.ReversibleTuring.Compression.encode_injective`, `Monodromy.ReversibleTuring.Compression.respects`, `Monodromy.ReversibleTuring.Compression.size`, `Monodromy.ReversibleTuring.Compression.table`.
-- source:
--   Authoritative local working-tree snapshot SHA-256 e03ce2d08e07ee663140bec213fb21e995f44153a3c556c908fcf1c8d6fefe6c; repository https://github.com/ERHUTUZI123/monodromy. The remote Git base is incomplete and is not asserted to contain these declarations.
--   src/Monodromy/FormalCompilation.lean (file SHA-256 c07335814044367fc4605d1e494fe82a30c684f754d58d55aaa7514b94c37122):
--   Monodromy.ReversibleTuring.Compression.result_iff at L1280-L1297 [UTF-8 67555:68690].

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
open Monodromy.ReversibleTuring.Compression
open Turing Counter.Reversible
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem Monodromy.ReversibleTuring.Compression.result_iff (machine : TM0.Machine (Fin a) (Fin q))
    (first last : TM0.Cfg (Fin a) (Fin q)) (history : ℕ) :
    (∃ finalHistory, Monodromy.ReversibleTuring.Compression.encode a q machine last finalHistory ∈
      Monodromy.Counter.Reversible.eval (Monodromy.ReversibleTuring.Compression.table a q machine) (Monodromy.ReversibleTuring.Compression.encode a q machine first history)) ↔
      last ∈ StateTransition.eval (TM0.step machine) first := by sorry
