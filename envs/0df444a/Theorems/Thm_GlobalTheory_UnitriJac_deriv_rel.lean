-- Prove2me | Theorems.Thm_GlobalTheory_UnitriJac_deriv_rel
-- name    : GlobalTheory.UnitriJac.deriv_rel
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:47:41.502956+00:00
-- url     : https://prove2.me/theorems/ed4d1942-4f0c-4018-9333-fce0a4538d7e
-- title:
--   Unitri Jac: deriv rel
-- statement:
--   The Unitri Jac construction uses the deriv rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L94-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L94-L146

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DifferentiableAtAdjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.UnitriJac
open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
noncomputable section

theorem GlobalTheory.UnitriJac.deriv_rel {r : ℕ} {N M b : ℂ → Matrix (Fin r) (Fin r) ℂ} {g N' M' : Matrix (Fin r) (Fin r) ℂ}
    (hN : ∀ i j, HasDerivAt (fun s => N s i j) (N' i j) 0)
    (hM : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) 0)
    (hMd : ∀ s, (M s).det = 1) (hNd : (N 0).det = 1) (hbd : (b 0).det ≠ 0)
    (h : ∀ᶠ s in 𝓝 (0 : ℂ), g * N s = M s * b s ∧ ∀ a c : Fin r, c < a → b s a c = 0)
    (a c : Fin r) (hca : c < a) :
    ((M 0)⁻¹ * M') a c = (b 0 * ((N 0)⁻¹ * N') * (b 0)⁻¹) a c := by sorry
