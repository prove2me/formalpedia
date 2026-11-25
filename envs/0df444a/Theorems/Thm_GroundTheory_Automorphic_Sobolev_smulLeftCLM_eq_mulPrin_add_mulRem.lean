-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_smulLeftCLM_eq_mulPrin_add_mulRem
-- name    : GroundTheory.Automorphic.Sobolev.smulLeftCLM_eq_mulPrin_add_mulRem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:50:14.214853+00:00
-- url     : https://prove2.me/theorems/6168a471-6dee-450f-b161-25e0df650372
-- title:
--   Sobolev: smul Left CLM eq mul Prin add mul Rem
-- statement:
--   The Sobolev construction uses the smul Left CLM eq mul Prin add mul Rem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L537-L539
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L537-L539

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

theorem GroundTheory.Automorphic.Sobolev.smulLeftCLM_eq_mulPrin_add_mulRem (χ : 𝓢(E, ℂ)) (r : ℝ) (u : 𝓢'(E, ℂ)) :
    smulLeftCLM ℂ (χ : E → ℂ) u = mulPrin χ r u + mulRem χ r u := by sorry
