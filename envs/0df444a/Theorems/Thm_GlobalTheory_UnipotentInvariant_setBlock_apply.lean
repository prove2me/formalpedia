-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentInvariant_setBlock_apply
-- name    : GlobalTheory.UnipotentInvariant.setBlock_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:54.092029+00:00
-- url     : https://prove2.me/theorems/1c5ab891-4902-4a73-b019-e1eb104e8d33
-- title:
--   Unipotent Invariant: set Block apply
-- statement:
--   The Unipotent Invariant construction uses the set Block apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L229-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L229-L231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ProdLeadMinorDiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory
open GlobalTheory.UnipotentInvariant
variable {K : Type*} [Field K] {p : ℕ}
variable {σ : Type*} [DecidableEq σ]
omit [Field K] [DecidableEq σ]

theorem GlobalTheory.UnipotentInvariant.setBlock_apply {z : Fin p × Fin p → σ} (hz : Function.Injective z) (x : σ → K)
    (M : Matrix (Fin p) (Fin p) K) (w : Fin p × Fin p) : setBlock z x M (z w) = M w.1 w.2 := by sorry
