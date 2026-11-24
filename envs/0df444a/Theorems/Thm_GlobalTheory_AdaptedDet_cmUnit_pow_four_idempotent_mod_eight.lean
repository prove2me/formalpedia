-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedDet_cmUnit_pow_four_idempotent_mod_eight
-- name    : GlobalTheory.AdaptedDet.cmUnit_pow_four_idempotent_mod_eight
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:22.169915+00:00
-- url     : https://prove2.me/theorems/683534b1-ca81-487a-a2a9-6ec9dd732065
-- title:
--   Adapted Det: cm Unit pow four idempotent mod eight
-- statement:
--   The Adapted Det construction uses the cm Unit pow four idempotent mod eight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmUnitPowFourIdempotentModEight.lean#L115-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmUnitPowFourIdempotentModEight.lean#L115-L139

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight
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
open GlobalTheory GlobalTheory.AdaptedDet

theorem GlobalTheory.AdaptedDet.cmUnit_pow_four_idempotent_mod_eight {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    H.w0 ^ 4 ≠ 0 ∧ ∃ t : 𝓞 E, H.w0 ^ 4 * H.w0 ^ 4 - H.w0 ^ 4 = (8 : ℕ) * t := by sorry
