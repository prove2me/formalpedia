-- Prove2me | Theorems.Thm_GlobalTheory_AnisoSize_absNorm_eq
-- name    : GlobalTheory.AnisoSize.absNorm_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:26.537742+00:00
-- url     : https://prove2.me/theorems/bf9bdccd-f307-4c3e-a584-bfdd2ec5c253
-- title:
--   Aniso Size: abs Norm eq
-- statement:
--   The Aniso Size construction uses the abs Norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L30-L33

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

theorem GlobalTheory.AnisoSize.absNorm_eq (a : 𝓞 E) :
    (Ideal.absNorm (Ideal.span {a}) : ℝ) = ∏ φ : E →+* ℂ, ‖φ (algebraMap (𝓞 E) E a)‖ := by sorry
