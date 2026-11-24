-- Prove2me | Theorems.Thm_GlobalTheory_sum_norm_sq_minors_eq_one
-- name    : GlobalTheory.sum_norm_sq_minors_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:44.400805+00:00
-- url     : https://prove2.me/theorems/cdaa4230-9076-452a-b281-2837c329ee62
-- title:
--   Global Theory: sum norm sq minors eq one
-- statement:
--   The Global Theory construction uses the sum norm sq minors eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L139-L143

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

theorem GlobalTheory.sum_norm_sq_minors_eq_one (A : Matrix (Fin i) n 𝕜) (hA : A * Aᴴ = 1) :
    ∑ S : Set.powersetCard n i, ‖(A.submatrix id (subsetEnum S)).det‖ ^ 2 = 1 := by sorry
