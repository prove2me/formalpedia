-- Prove2me | Theorems.Thm_GlobalTheory_SpanIndex_relIndex_mul_le_of_le
-- name    : GlobalTheory.SpanIndex.relIndex_mul_le_of_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:18:43.028744+00:00
-- url     : https://prove2.me/theorems/d6e122e7-6266-41aa-9cf1-601adec3eea7
-- title:
--   Span Index: rel Index mul le of le
-- statement:
--   The Span Index construction uses the rel Index mul le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RelIndexIntegralSpanSupermultiplicative.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RelIndexIntegralSpanSupermultiplicative.lean#L15-L22

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

theorem GlobalTheory.SpanIndex.relIndex_mul_le_of_le {A : Type} [AddCommGroup A] (M₁ M₂ W₁ W₂ Λ : AddSubgroup A)
    (h₁ : M₁ ≤ Λ ⊓ W₁) (h₂ : M₂ ≤ Λ ⊓ W₂)
    (hne : (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) ≠ 0) :
    M₁.relIndex (Λ ⊓ W₁) * M₂.relIndex (Λ ⊓ W₂) ≤
      (M₁ ⊓ M₂).relIndex (Λ ⊓ (W₁ ⊓ W₂)) * (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) := by sorry
