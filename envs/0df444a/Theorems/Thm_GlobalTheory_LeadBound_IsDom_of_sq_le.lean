-- Prove2me | Theorems.Thm_GlobalTheory_LeadBound_IsDom_of_sq_le
-- name    : GlobalTheory.LeadBound.IsDom.of_sq_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T02:46:20.491893+00:00
-- url     : https://prove2.me/theorems/a6bceeae-72ea-45af-92a8-5b60dbf03440
-- title:
--   Is Dom: of sq le
-- statement:
--   The Is Dom construction uses the of sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MulProd.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MulProd.lean#L90-L96

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

theorem GlobalTheory.LeadBound.IsDom.of_sq_le {W : Frame X.Ψ r → ℝ} {la : Wt X.Ψ r}
    {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) {K : ℝ} (hW : ∀ x, 0 ≤ W x)
    (hK : ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ K * W x) :
    IsDom X (fun x => Real.sqrt (W x)) la 1 P := by sorry
