-- Prove2me | Theorems.Thm_GlobalTheory_exists_two_rpow_le_norm_minor
-- name    : GlobalTheory.exists_two_rpow_le_norm_minor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:55:42.990907+00:00
-- url     : https://prove2.me/theorems/0fbad6ef-7d20-4c1e-8074-edb0d105426f
-- title:
--   Global Theory: exists two rpow le norm minor
-- statement:
--   The Global Theory construction uses the exists two rpow le norm minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L180-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L180-L185

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

theorem GlobalTheory.exists_two_rpow_le_norm_minor (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) {r : ℕ}
    (hr : Fintype.card n ≤ r) :
    ∃ S : Set.powersetCard n i,
      (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ ‖(A.submatrix id (subsetEnum S)).det‖ := by sorry
