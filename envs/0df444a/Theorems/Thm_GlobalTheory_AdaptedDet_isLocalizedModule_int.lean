-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedDet_isLocalizedModule_int
-- name    : GlobalTheory.AdaptedDet.isLocalizedModule_int
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:53:31.42081+00:00
-- url     : https://prove2.me/theorems/a53d3072-15f2-4277-abce-936c4f848771
-- title:
--   Adapted Det: is Localized Module int
-- statement:
--   The Adapted Det construction uses the is Localized Module int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmUnitPowFourIdempotentModEight.lean#L145-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmUnitPowFourIdempotentModEight.lean#L145-L158

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
variable {E : Type} [Field E] [NumberField E] {L : Type} [AddCommGroup L] [Module (𝓞 E) L] {r : ℕ}

theorem GlobalTheory.AdaptedDet.isLocalizedModule_int (φ : L →ₗ[𝓞 E] (Fin r → E)) (hf : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤) :
    IsLocalizedModule ℤ⁰ (φ.restrictScalars ℤ) := by sorry
