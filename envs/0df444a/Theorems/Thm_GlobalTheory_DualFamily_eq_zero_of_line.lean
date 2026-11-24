-- Prove2me | Theorems.Thm_GlobalTheory_DualFamily_eq_zero_of_line
-- name    : GlobalTheory.DualFamily.eq_zero_of_line
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:51:13.351479+00:00
-- url     : https://prove2.me/theorems/65822d10-c240-4e81-8960-0416952617d2
-- title:
--   Dual Family: eq zero of line
-- statement:
--   The Dual Family construction uses the eq zero of line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean#L57-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean#L57-L67

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
omit [IsCMField E]

theorem GlobalTheory.DualFamily.eq_zero_of_line {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (w : Fin n → E) (hw : ∀ c : E, c • w ∈ Λ) : w = 0 := by sorry
