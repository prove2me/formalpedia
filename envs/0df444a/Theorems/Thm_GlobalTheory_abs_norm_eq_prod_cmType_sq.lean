-- Prove2me | Theorems.Thm_GlobalTheory_abs_norm_eq_prod_cmType_sq
-- name    : GlobalTheory.abs_norm_eq_prod_cmType_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:44.38981+00:00
-- url     : https://prove2.me/theorems/c87712a8-6808-47e3-9a8f-3f649af46c60
-- title:
--   Global Theory: abs norm eq prod cm Type sq
-- statement:
--   The Global Theory construction uses the abs norm eq prod cm Type sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/AbsNormEqProdCmTypeSq.lean#L11-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/AbsNormEqProdCmTypeSq.lean#L11-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_AbsNormEqProdCmTypeSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory

theorem GlobalTheory.abs_norm_eq_prod_cmType_sq :
    (∀ (r : ℕ) (X : Data E r) (z : E), ((|Algebra.norm ℚ z| : ℚ) : ℝ) = ∏ τ : X.Ψ, ‖τ.1 z‖ ^ 2) := by sorry
