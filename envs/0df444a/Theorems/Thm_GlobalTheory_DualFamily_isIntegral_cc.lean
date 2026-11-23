-- Prove2me | Theorems.Thm_GlobalTheory_DualFamily_isIntegral_cc
-- name    : GlobalTheory.DualFamily.isIntegral_cc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:42.62255+00:00
-- url     : https://prove2.me/theorems/2492bd2b-626c-4b02-8e08-340e653e397f
-- title:
--   Dual Family: is Integral cc
-- statement:
--   The Dual Family construction uses the is Integral cc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/IsLocalizedModuleSubtype.lean#L35-L38

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

theorem GlobalTheory.DualFamily.isIntegral_cc {a : E} (ha : IsIntegral ℤ a) :
    IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc a) := by sorry
