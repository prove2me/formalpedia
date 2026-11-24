-- Prove2me | Theorems.Thm_GlobalTheory_SympMod_exists_stdSymp_zmod
-- name    : GlobalTheory.SympMod.exists_stdSymp_zmod
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:25:23.307302+00:00
-- url     : https://prove2.me/theorems/632604e6-778c-45cc-a201-034adf5faec2
-- title:
--   Symp Mod: exists std Symp zmod
-- statement:
--   The Symp Mod construction uses the exists std Symp zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsStdSympZmod.lean#L149-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsStdSympZmod.lean#L149-L164

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsStdSympZmod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.SympMod
open ReciprocityTheory.ChartRestriction.G.Out

theorem GlobalTheory.SympMod.exists_stdSymp_zmod {M g : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (hB : B.IsAlt) (hN : ∀ x, (∀ y, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // d • x = 0} = d ^ (2 * g)) :
    ∃ v : Fin (2 * g) → V, ∀ i k, B (v i) (v k) = (stdSymp g i k : ℤ) := by sorry
