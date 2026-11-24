-- Prove2me | Theorems.Thm_GlobalTheory_MajorantOrthFrame_maj_eq_sum_norm_sq_of_isOrth
-- name    : GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:20:15.954494+00:00
-- url     : https://prove2.me/theorems/2b9080ee-763c-4821-85db-b1b3e257030d
-- title:
--   Majorant Orth Frame: maj eq sum norm sq of is Orth
-- statement:
--   The Majorant Orth Frame construction uses the maj eq sum norm sq of is Orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajorantEqSumNormSqOrthonormalFrame.lean#L30-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MajorantEqSumNormSqOrthonormalFrame.lean#L30-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrame
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
open GlobalTheory GlobalTheory.MajorantOrthFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
      (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ),
        X.maj x τ v = ∑ a, ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹.mulVec v) a‖ ^ 2) := by sorry
