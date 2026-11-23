-- Prove2me | Theorems.Thm_GlobalTheory_norm_entry_le_of_gram_eq_smul_one
-- name    : GlobalTheory.norm_entry_le_of_gram_eq_smul_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:23.828069+00:00
-- url     : https://prove2.me/theorems/1d81e3f4-fe65-4dd6-9e59-ff0370a4102f
-- title:
--   Global Theory: norm entry le of gram eq smul one
-- statement:
--   The Global Theory construction uses the norm entry le of gram eq smul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OrthonormalFramesBoundedOfDefinite.lean#L14-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OrthonormalFramesBoundedOfDefinite.lean#L14-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OrthonormalFramesBoundedOfDefinite
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
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.norm_entry_le_of_gram_eq_smul_one {r : ℕ} (G x : Matrix (Fin r) (Fin r) ℂ) (s : ℂ)
    (hs : s * s = 1) (h : xᵀ * G * x.map (starRingEnd ℂ) = s • (1 : Matrix (Fin r) (Fin r) ℂ))
    (a b : Fin r) : ‖x a b‖ ≤ 1 + ‖G⁻¹ a a‖ := by sorry
