-- Prove2me | Theorems.Thm_GlobalTheory_AnisoSize_house_inv_le
-- name    : GlobalTheory.AnisoSize.house_inv_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:58:18.959995+00:00
-- url     : https://prove2.me/theorems/40ca8a8b-95aa-4036-99c6-c6d60227d704
-- title:
--   Aniso Size: house inv le
-- statement:
--   The Aniso Size construction uses the house inv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L40-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L40-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.AnisoSize.house_inv_le {a : E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0) {T : ℝ} (hT : 1 ≤ T)
    (h : house a ≤ T) : house a⁻¹ ≤ T ^ finrank ℚ E := by sorry
