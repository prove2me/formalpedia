-- Prove2me | Theorems.Thm_GlobalTheory_JacobianIndependence_eq_zero_of_det_fderiv_ne_zero
-- name    : GlobalTheory.JacobianIndependence.eq_zero_of_det_fderiv_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:49.809672+00:00
-- url     : https://prove2.me/theorems/c3f5043f-5690-43e8-87de-72b21c51a0df
-- title:
--   Jacobian Independence: eq zero of det fderiv ne zero
-- statement:
--   The Jacobian Independence construction uses the eq zero of det fderiv ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EqZeroOfDetFderivNeZero.lean#L25-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EqZeroOfDetFderivNeZero.lean#L25-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfDetFderivNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open Filter Topology
open GlobalTheory GlobalTheory.JacobianIndependence

theorem GlobalTheory.JacobianIndependence.eq_zero_of_det_fderiv_ne_zero :
    ∀ (n : ℕ) (f : Fin n → V n → ℂ), (∀ k, ∀ᶠ z in nhds (0 : V n), DifferentiableAt ℂ (f k) z) →
      (fderiv ℂ (fun z : V n => (WithLp.toLp 2 fun k => f k z : V n)) 0).det ≠ 0 →
      ∀ p : MvPolynomial (Fin n) ℂ,
        (∀ᶠ z in nhds (0 : V n), MvPolynomial.eval (fun k => f k z) p = 0) → p = 0 := by sorry
