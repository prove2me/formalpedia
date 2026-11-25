-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_iteratedLineDeriv_eq_fourierMultiplier
-- name    : GroundTheory.Automorphic.Sobolev.iteratedLineDeriv_eq_fourierMultiplier
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:02:27.562658+00:00
-- url     : https://prove2.me/theorems/c9a731b5-13df-4713-b632-b7c3badcbc1e
-- title:
--   Sobolev: iterated Line Deriv eq fourier Multiplier
-- statement:
--   The Sobolev construction uses the iterated Line Deriv eq fourier Multiplier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L316-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticOperators.lean#L316-L330

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem GroundTheory.Automorphic.Sobolev.iteratedLineDeriv_eq_fourierMultiplier {k : ℕ} (w : Fin k → E) (u : 𝓢'(E, ℂ)) :
    ∂^{w} u = fourierMultiplierCLM ℂ (derivSymb w) u := by sorry
