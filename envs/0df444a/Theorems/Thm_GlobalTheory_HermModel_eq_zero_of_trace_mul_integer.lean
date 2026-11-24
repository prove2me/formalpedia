-- Prove2me | Theorems.Thm_GlobalTheory_HermModel_eq_zero_of_trace_mul_integer
-- name    : GlobalTheory.HermModel.eq_zero_of_trace_mul_integer
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:19:38.432043+00:00
-- url     : https://prove2.me/theorems/5fcede20-eb42-4a52-ae75-6e80050c57e4
-- title:
--   Herm Model: eq zero of trace mul integer
-- statement:
--   The Herm Model construction uses the eq zero of trace mul integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/FinrankEqOfInjectiveOfSpan.lean#L48-L54

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HermModel
variable {E : Type} [Field E] [NumberField E]
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.HermModel.eq_zero_of_trace_mul_integer {t : E}
    (ht : ∀ a : 𝓞 E, Algebra.trace ℚ E (t * a) = 0) : t = 0 := by sorry
