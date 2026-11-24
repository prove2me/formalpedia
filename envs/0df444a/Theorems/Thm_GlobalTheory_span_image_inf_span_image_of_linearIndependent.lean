-- Prove2me | Theorems.Thm_GlobalTheory_span_image_inf_span_image_of_linearIndependent
-- name    : GlobalTheory.span_image_inf_span_image_of_linearIndependent
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:13.179424+00:00
-- url     : https://prove2.me/theorems/e0ef0051-6e5f-4ceb-a08e-37120aa9ea24
-- title:
--   Global Theory: span image inf span image of linear Independent
-- statement:
--   The Global Theory construction uses the span image inf span image of linear Independent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/SpanImageInfSpanImageOfLinearIndependent.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/SpanImageInfSpanImageOfLinearIndependent.lean#L9-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SpanImageInfSpanImageOfLinearIndependent
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
open GlobalTheory

theorem GlobalTheory.span_image_inf_span_image_of_linearIndependent {R V ι : Type} [CommRing R]
    [AddCommGroup V] [Module R V] {w : ι → V} (hw : LinearIndependent R w) (s t : Set ι) :
    Submodule.span R (w '' s) ⊓ Submodule.span R (w '' t) = Submodule.span R (w '' (s ∩ t)) := by sorry
