-- Prove2me | Theorems.Thm_GlobalTheory_DualFamily_exists_herm_eq
-- name    : GlobalTheory.DualFamily.exists_herm_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:19.48443+00:00
-- url     : https://prove2.me/theorems/685c505a-27e0-433e-ae75-f5f959cc9121
-- title:
--   Dual Family: exists herm eq
-- statement:
--   The Dual Family construction uses the exists herm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean#L44-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean#L44-L50

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

theorem GlobalTheory.DualFamily.exists_herm_eq {n : ℕ} (f : (Fin n → E) →ₗ[E] E) :
    ∃ w : Fin n → E, ∀ u, f u = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 u w := by sorry
