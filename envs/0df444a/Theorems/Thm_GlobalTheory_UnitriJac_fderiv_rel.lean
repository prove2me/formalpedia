-- Prove2me | Theorems.Thm_GlobalTheory_UnitriJac_fderiv_rel
-- name    : GlobalTheory.UnitriJac.fderiv_rel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:20.8038+00:00
-- url     : https://prove2.me/theorems/f47fb48c-3df3-4fa9-8d5e-aec99888db33
-- title:
--   Unitri Jac: fderiv rel
-- statement:
--   The Unitri Jac construction uses the fderiv rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L164-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L164-L203

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.UnitriJac.fderiv_rel {r : ℕ} (X : Data E r) (x0 x1 : Frame X.Ψ r) (γ : GL (Fin r) E) (U : Set (V (nd X)))
    (Φ : V (nd X) → V (nd X)) (bf : V (nd X) → Frame X.Ψ r) (hU : IsOpen U)
    (hΦ : DifferentiableOn ℂ Φ U)
    (h : ∀ z ∈ U, cpt X x0 z ∈ X.dom ∧ bf z ∈ Bor X.Ψ r ∧
      cpt X x0 z = lact γ (rmul (cpt X x1 (Φ z)) (bf z)))
    (z : V (nd X)) (hz : z ∈ U) (v : V (nd X)) (τ : X.Ψ) :
    leftM (mat (nmat X (Φ z)) τ)⁻¹ *ᵥ crd X (fderiv ℂ Φ z v) τ =
      (adM (mat (bf z) τ) * leftM (mat (nmat X z) τ)⁻¹) *ᵥ crd X v τ := by sorry
