-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_fourier_expChar_smul_fourierInv
-- name    : GroundTheory.Automorphic.Sobolev.fourier_expChar_smul_fourierInv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:55:32.65094+00:00
-- url     : https://prove2.me/theorems/56624f5e-3c84-4f8f-ab93-d76415e59f99
-- title:
--   Sobolev: fourier exp Char smul fourier Inv
-- statement:
--   The Sobolev construction uses the fourier exp Char smul fourier Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L63-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/SobolevFriedrichs.lean#L63-L75

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevFriedrichs
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
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem GroundTheory.Automorphic.Sobolev.fourier_expChar_smul_fourierInv (h : E) (φ : 𝓢(E, ℂ)) :
    𝓕 (SchwartzMap.smulLeftCLM ℂ (expChar (-h)) (𝓕⁻ φ)) = SchwartzMap.compSubConstCLM ℂ (-h) φ := by sorry
