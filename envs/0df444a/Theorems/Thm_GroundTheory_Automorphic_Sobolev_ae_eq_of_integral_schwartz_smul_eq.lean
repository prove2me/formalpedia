-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_ae_eq_of_integral_schwartz_smul_eq
-- name    : GroundTheory.Automorphic.Sobolev.ae_eq_of_integral_schwartz_smul_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:44.848924+00:00
-- url     : https://prove2.me/theorems/23adb8c4-af58-4f6f-867f-848110ed3bf4
-- title:
--   Sobolev: ae eq of integral schwartz smul eq
-- statement:
--   The Sobolev construction uses the ae eq of integral schwartz smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L439-L458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/Sobolev.lean#L439-L458

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

theorem GroundTheory.Automorphic.Sobolev.ae_eq_of_integral_schwartz_smul_eq {g₁ g₂ : E → F}
    (h₁ : LocallyIntegrable g₁ (volume : Measure E)) (h₂ : LocallyIntegrable g₂ (volume : Measure E))
    (h : ∀ φ : 𝓢(E, ℂ), HasCompactSupport φ → ∫ x, φ x • g₁ x = ∫ x, φ x • g₂ x) :
    g₁ =ᵐ[volume] g₂ := by sorry
