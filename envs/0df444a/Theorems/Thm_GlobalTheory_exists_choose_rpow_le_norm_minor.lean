-- Prove2me | Theorems.Thm_GlobalTheory_exists_choose_rpow_le_norm_minor
-- name    : GlobalTheory.exists_choose_rpow_le_norm_minor
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:30:42.037803+00:00
-- url     : https://prove2.me/theorems/63f1834c-f63d-46f8-be65-41b467fef8d0
-- title:
--   Global Theory: exists choose rpow le norm minor
-- statement:
--   The Global Theory construction uses the exists choose rpow le norm minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L155-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L155-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [LinearOrder n] {i : ℕ}

theorem GlobalTheory.exists_choose_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    i ≤ Fintype.card n ∧ ∃ S : Set.powersetCard n i,
      ((Fintype.card n).choose i : ℝ) ^ (-(1 : ℝ) / 2) ≤
        ‖(A.submatrix id (subsetEnum S)).det‖ := by sorry
