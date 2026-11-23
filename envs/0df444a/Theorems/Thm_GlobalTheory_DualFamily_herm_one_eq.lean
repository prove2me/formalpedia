-- Prove2me | Theorems.Thm_GlobalTheory_DualFamily_herm_one_eq
-- name    : GlobalTheory.DualFamily.herm_one_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:30.677442+00:00
-- url     : https://prove2.me/theorems/d4efdcb6-d694-49a9-8327-35d0e41a228f
-- title:
--   Dual Family: herm one eq
-- statement:
--   The Dual Family construction uses the herm one eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean#L16-L19

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

theorem GlobalTheory.DualFamily.herm_one_eq {n : ℕ} (x y : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y = ∑ a, x a * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y a) := by sorry
