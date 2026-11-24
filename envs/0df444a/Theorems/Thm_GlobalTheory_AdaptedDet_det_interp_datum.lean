-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedDet_det_interp_datum
-- name    : GlobalTheory.AdaptedDet.det_interp_datum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:17.073794+00:00
-- url     : https://prove2.me/theorems/37dff47e-b367-43d9-a4e7-5e9f56dd35eb
-- title:
--   Adapted Det: det interp datum
-- statement:
--   The Adapted Det construction uses the det interp datum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmUnitPowFourIdempotentModEight.lean#L206-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmUnitPowFourIdempotentModEight.lean#L206-L297

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

theorem GlobalTheory.AdaptedDet.det_interp_datum {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {M : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (hM : 3 ≤ M) (hiso : ∀ a b, D.EF (gam a) (gam b) = D.EF a b)
    (hlev : ∀ a, ∃ e, gam a = a + M • e) (T : D.La →ₗ[ℤ] D.La)
    (hT : ∀ x, T x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x)) :
    (((LinearMap.toMatrix b b T).det : ℤ) : ZMod 8) = 1 := by sorry
