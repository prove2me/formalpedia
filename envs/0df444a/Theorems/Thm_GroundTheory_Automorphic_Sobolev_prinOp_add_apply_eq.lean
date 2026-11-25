-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_prinOp_add_apply_eq
-- name    : GroundTheory.Automorphic.Sobolev.prinOp_add_apply_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:25.108942+00:00
-- url     : https://prove2.me/theorems/f64b8cc1-ecc5-4ad7-b40e-132285c76069
-- title:
--   Sobolev: prin Op add apply eq
-- statement:
--   The Sobolev construction uses the prin Op add apply eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L392-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/EllipticLocal.lean#L392-L407

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

theorem GroundTheory.Automorphic.Sobolev.prinOp_add_apply_eq (hNl : IsLocal N) {δ ρ : ℝ} (hδ : 0 < δ) (hρ : ρ < δ) {u : 𝓢'(E, ℂ)}
    (hu : Distribution.IsVanishingOn u (Metric.closedBall x₀ ρ)ᶜ) :
    (prinOp a w + N) u = P0 a w x₀ u + locM a w N x₀ hδ u := by sorry
