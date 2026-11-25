-- Prove2me | Theorems.Thm_GlobalTheory_T_relIndex_integralSpan_supermultiplicative
-- name    : GlobalTheory.T.relIndex_integralSpan_supermultiplicative
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:56:28.80671+00:00
-- url     : https://prove2.me/theorems/39f9065c-419a-4cf9-b813-31e2eb76a781
-- title:
--   T: rel Index integral Span supermultiplicative
-- statement:
--   The T construction uses the rel Index integral Span supermultiplicative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RelIndexIntegralSpanSupermultiplicativeStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RelIndexIntegralSpanSupermultiplicativeStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexIntegralSpanSupermultiplicative
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexIntegralSpanSupermultiplicativeStatement
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

theorem GlobalTheory.T.relIndex_integralSpan_supermultiplicative : (∀ (r : ℕ) (X : Data E r) (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (w : α ⊕ β ⊕ γ → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup)) ≤ ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup))) := by sorry
