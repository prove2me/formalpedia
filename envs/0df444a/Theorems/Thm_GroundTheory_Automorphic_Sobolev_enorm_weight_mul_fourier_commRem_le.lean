-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_enorm_weight_mul_fourier_commRem_le
-- name    : GroundTheory.Automorphic.Sobolev.enorm_weight_mul_fourier_commRem_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:13:17.909731+00:00
-- url     : https://prove2.me/theorems/046f744d-404f-502e-8452-0a691a405133
-- title:
--   Sobolev: enorm weight mul fourier comm Rem le
-- statement:
--   The Sobolev construction uses the enorm weight mul fourier comm Rem le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L305-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L305-L343

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevRellich
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevEmbedding
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable (χ : 𝓢(E, ℂ))

theorem GroundTheory.Automorphic.Sobolev.enorm_weight_mul_fourier_commRem_le (r a : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    ‖weight (r + a) ξ * (𝓕 (commRem χ r φ) : 𝓢(E, ℂ)) ξ‖ₑ ≤
      ∫⁻ η, ENNReal.ofReal (commConst r a) * wK ((|a| + |r - 1| + 1) / 2) (𝓕 χ) (ξ - η) *
        ‖weight (r + a - 1) η * (𝓕 φ : 𝓢(E, ℂ)) η‖ₑ := by sorry
