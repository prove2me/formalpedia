-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_mulRem_coe
-- name    : GroundTheory.Automorphic.Sobolev.mulRem_coe
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:13:50.770382+00:00
-- url     : https://prove2.me/theorems/5dbaef6c-4ed1-43e2-9d05-8b781970bda1
-- title:
--   Sobolev: mul Rem coe
-- statement:
--   The Sobolev construction uses the mul Rem coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L549-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevMultiplication.lean#L549-L551

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

theorem GroundTheory.Automorphic.Sobolev.mulRem_coe (χ : 𝓢(E, ℂ)) (r : ℝ) (φ : 𝓢(E, ℂ)) :
    mulRem χ r (φ : 𝓢'(E, ℂ)) = ((commRem χ r φ : 𝓢(E, ℂ)) : 𝓢'(E, ℂ)) := by sorry
