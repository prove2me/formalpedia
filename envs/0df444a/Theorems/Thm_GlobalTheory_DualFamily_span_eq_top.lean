-- Prove2me | Theorems.Thm_GlobalTheory_DualFamily_span_eq_top
-- name    : GlobalTheory.DualFamily.span_eq_top
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:33.287489+00:00
-- url     : https://prove2.me/theorems/0cee0cd0-3c78-4892-b73e-49ef2875c7c2
-- title:
--   Dual Family: span eq top
-- statement:
--   The Dual Family construction uses the span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean#L72-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean#L72-L88

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory.DualFamily
open NumberField
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.DualFamily.span_eq_top {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by sorry
