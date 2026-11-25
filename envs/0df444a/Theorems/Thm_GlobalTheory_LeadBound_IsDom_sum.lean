-- Prove2me | Theorems.Thm_GlobalTheory_LeadBound_IsDom_sum
-- name    : GlobalTheory.LeadBound.IsDom.sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:49:37.875165+00:00
-- url     : https://prove2.me/theorems/a0adcea1-459a-49c6-813f-fb4b46386dae
-- title:
--   Is Dom: sum
-- statement:
--   The Is Dom construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MulProd.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MulProd.lean#L66-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BoundedSectionAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MulProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.LeadBound
open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {r : ℕ} (X : Data E r) (g : Frame X.Ψ r → ℝ)
variable {X g}

theorem GlobalTheory.LeadBound.IsDom.sum {ι : Type*} (S : Finset ι) {la : Wt X.Ψ r} {n : ℕ} {P : ι → Frame X.Ψ r → ℂ}
    (hP : ∀ i ∈ S, IsDom X g la n (P i)) : IsDom X g la n (∑ i ∈ S, P i) := by sorry
