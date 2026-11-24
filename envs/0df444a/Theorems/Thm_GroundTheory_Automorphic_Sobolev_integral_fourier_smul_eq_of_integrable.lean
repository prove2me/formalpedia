-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_integral_fourier_smul_eq_of_integrable
-- name    : GroundTheory.Automorphic.Sobolev.integral_fourier_smul_eq_of_integrable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:34:09.609368+00:00
-- url     : https://prove2.me/theorems/7b5ae4a0-6034-4b96-beb2-819c84247d9a
-- title:
--   Sobolev: integral fourier smul eq of integrable
-- statement:
--   The Sobolev construction uses the integral fourier smul eq of integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L460-L464
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L460-L464

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
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
variable {m : E → ℂ} {C s t : ℝ}

theorem GroundTheory.Automorphic.Sobolev.integral_fourier_smul_eq_of_integrable (φ : 𝓢(E, ℂ)) {g : E → F}
    (hg : Integrable g (volume : Measure E)) :
    ∫ ξ, 𝓕 φ ξ • g ξ = ∫ x, φ x • 𝓕 g x := by sorry
