-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_inner_proj_right
-- name    : GlobalTheory.RealWeil.inner_proj_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:29:44.596818+00:00
-- url     : https://prove2.me/theorems/e1063d3e-58fa-4f56-8f07-3d49919a3cf5
-- title:
--   Real Weil: inner proj right
-- statement:
--   The Real Weil construction uses the inner proj right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfOrthogonalTranslatesProj.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfOrthogonalTranslatesProj.lean#L33-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfOrthogonalTranslatesProj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
open scoped InnerProductSpace Real
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → H →L[ℂ] H}

theorem GlobalTheory.RealWeil.inner_proj_right {om : V → V → ℝ} (h : IsHeis om ρ) (x y : H) :
    ⟪x, proj h y⟫_ℂ = ∫ u, gau u * ⟪x, ρ u y⟫_ℂ := by sorry
