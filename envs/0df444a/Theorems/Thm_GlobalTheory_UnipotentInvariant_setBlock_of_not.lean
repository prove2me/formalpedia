-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentInvariant_setBlock_of_not
-- name    : GlobalTheory.UnipotentInvariant.setBlock_of_not
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:47:52.672594+00:00
-- url     : https://prove2.me/theorems/3230e861-9481-445a-bf2c-c19e60fe968b
-- title:
--   Unipotent Invariant: set Block of not
-- statement:
--   The Unipotent Invariant construction uses the set Block of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L234-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ProdLeadMinorDiagonal.lean#L234-L236

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

theorem GlobalTheory.UnipotentInvariant.setBlock_of_not {z : Fin p × Fin p → σ} (x : σ → K)
    (M : Matrix (Fin p) (Fin p) K) {s : σ} (hs : ¬ ∃ w, z w = s) : setBlock z x M s = x s := by sorry
