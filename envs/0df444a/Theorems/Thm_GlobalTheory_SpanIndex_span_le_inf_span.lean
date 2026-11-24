-- Prove2me | Theorems.Thm_GlobalTheory_SpanIndex_span_le_inf_span
-- name    : GlobalTheory.SpanIndex.span_le_inf_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:18:25.734475+00:00
-- url     : https://prove2.me/theorems/2b9ff68d-8c8d-4bad-9be4-a088af1e2fe3
-- title:
--   Span Index: span le inf span
-- statement:
--   The Span Index construction uses the span le inf span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RelIndexIntegralSpanSupermultiplicative.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RelIndexIntegralSpanSupermultiplicative.lean#L26-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSupMulRelIndexInfSame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SpanImageInfSpanImageOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexIntegralSpanSupermultiplicative
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
open GlobalTheory GlobalTheory.SpanIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]

theorem GlobalTheory.SpanIndex.span_le_inf_span {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) {ι : Type}
    (w : ι → Fin r → E) (hw : ∀ a, w a ∈ Λ) :
    (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup ≤
      Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup := by sorry
