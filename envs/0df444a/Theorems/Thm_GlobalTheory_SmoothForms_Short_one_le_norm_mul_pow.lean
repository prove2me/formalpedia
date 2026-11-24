-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_Short_one_le_norm_mul_pow
-- name    : GlobalTheory.SmoothForms.Short.one_le_norm_mul_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:19:32.167826+00:00
-- url     : https://prove2.me/theorems/68d0cd52-216c-4e2b-8e0b-5175359ceacb
-- title:
--   Short: one le norm mul pow
-- statement:
--   The Short construction uses the one le norm mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean#L9-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms GlobalTheory.HermClass Module Submodule NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Short

theorem GlobalTheory.SmoothForms.Short.one_le_norm_mul_pow {E : Type} [Field E] [NumberField E] {a : E} (ha : IsIntegral ℤ a) (h0 : a ≠ 0)
    {T : ℝ} (hT : 1 ≤ T) (haT : house a ≤ T) (ψ : E →+* ℂ) : 1 ≤ ‖ψ a‖ * T ^ finrank ℚ E := by sorry
