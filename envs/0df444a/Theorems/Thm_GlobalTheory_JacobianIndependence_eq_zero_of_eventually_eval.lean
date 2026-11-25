-- Prove2me | Theorems.Thm_GlobalTheory_JacobianIndependence_eq_zero_of_eventually_eval
-- name    : GlobalTheory.JacobianIndependence.eq_zero_of_eventually_eval
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:47:05.827834+00:00
-- url     : https://prove2.me/theorems/395e213d-c5a1-4c3e-bc2c-1201dce35981
-- title:
--   Jacobian Independence: eq zero of eventually eval
-- statement:
--   The Jacobian Independence construction uses the eq zero of eventually eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EqZeroOfDetFderivNeZero.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/EqZeroOfDetFderivNeZero.lean#L11-L23

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

theorem GlobalTheory.JacobianIndependence.eq_zero_of_eventually_eval {n : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (a : EuclideanSpace ℂ (Fin n))
    (h : ∀ᶠ w in 𝓝 a, MvPolynomial.eval (fun k => w k) p = 0) : p = 0 := by sorry
