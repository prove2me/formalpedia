-- Prove2me | Theorems.Thm_GlobalTheory_SharpGradient_rhF_eq_sum_re
-- name    : GlobalTheory.SharpGradient.rhF_eq_sum_re
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:40:59.449618+00:00
-- url     : https://prove2.me/theorems/50acbb99-110f-4c5c-b86e-1fef27aacd42
-- title:
--   Sharp Gradient: rh F eq sum re
-- statement:
--   The Sharp Gradient construction uses the rh F eq sum re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean#L293-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ContinuousInvLeadingBlockEntry.lean#L293-L300

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_RhGradStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExhaustFStatementPfE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ContinuousInvLeadingBlockEntry
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_re

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
open GlobalTheory GlobalTheory.SharpGradient
open Filter Matrix
open scoped ComplexOrder ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SharpGradient.rhF_eq_sum_re {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)}
    (hz : z ∈ OmF X x0) :
    rhF X x0 z = ∑ τ, -Real.log (1 - ExF.Zt X z τ * (ExF.Zt X z τ)ᴴ).det.re := by sorry
