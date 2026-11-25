-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_exists_coeff_small
-- name    : GroundTheory.Automorphic.Sobolev.exists_coeff_small
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:20:10.860178+00:00
-- url     : https://prove2.me/theorems/2194c723-bb65-502a-b94d-a99b71170b86
-- title:
--   Sobolev: exists coeff small
-- statement:
--   The Sobolev construction uses the exists coeff small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L589-L600
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L589-L600

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
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
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (N : 𝓢'(E, ℂ) →L[ℂ] 𝓢'(E, ℂ))
  (x₀ : E)

theorem GroundTheory.Automorphic.Sobolev.exists_coeff_small {η : ℝ} (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ ∀ i, ∀ y ∈ Metric.closedBall x₀ (2 * δ), ‖a i y - a i x₀‖ ≤ η := by sorry
