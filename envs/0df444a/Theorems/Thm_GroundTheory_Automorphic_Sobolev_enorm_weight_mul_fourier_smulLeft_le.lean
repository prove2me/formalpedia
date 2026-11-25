-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_enorm_weight_mul_fourier_smulLeft_le
-- name    : GroundTheory.Automorphic.Sobolev.enorm_weight_mul_fourier_smulLeft_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:13:42.06865+00:00
-- url     : https://prove2.me/theorems/3691c050-4741-4576-be0b-9ea037ebee2c
-- title:
--   Sobolev: enorm weight mul fourier smul Left le
-- statement:
--   The Sobolev construction uses the enorm weight mul fourier smul Left le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L231-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L231-L246

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

theorem GroundTheory.Automorphic.Sobolev.enorm_weight_mul_fourier_smulLeft_le (r : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    ‖weight r ξ * (𝓕 (SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) φ) : 𝓢(E, ℂ)) ξ‖ₑ ≤
      ∫⁻ η, ENNReal.ofReal (2 ^ (|r| / 2)) * wK (|r| / 2) (𝓕 χ) (ξ - η) *
        ‖weight r η * (𝓕 φ : 𝓢(E, ℂ)) η‖ₑ := by sorry
