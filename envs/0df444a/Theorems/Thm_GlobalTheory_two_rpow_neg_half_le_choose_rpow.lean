-- Prove2me | Theorems.Thm_GlobalTheory_two_rpow_neg_half_le_choose_rpow
-- name    : GlobalTheory.two_rpow_neg_half_le_choose_rpow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:28.835266+00:00
-- url     : https://prove2.me/theorems/e71999e3-b316-4907-a491-6247710997be
-- title:
--   Global Theory: two rpow neg half le choose rpow
-- statement:
--   The Global Theory construction uses the two rpow neg half le choose rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L145-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/MulConjTransposeEqOneOfOrthonormal.lean#L145-L153

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

theorem GlobalTheory.two_rpow_neg_half_le_choose_rpow {i N r : ℕ} (hi : i ≤ N) (hr : N ≤ r) :
    (2 : ℝ) ^ (-(r : ℝ) / 2) ≤ (N.choose i : ℝ) ^ (-(1 : ℝ) / 2) := by sorry
