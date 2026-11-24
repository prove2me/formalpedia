-- Prove2me | Theorems.Thm_GlobalTheory_SympMod_exists_pair_eq_one
-- name    : GlobalTheory.SympMod.exists_pair_eq_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:25:07.360862+00:00
-- url     : https://prove2.me/theorems/d115106b-fc12-400d-ac39-67252485cafd
-- title:
--   Symp Mod: exists pair eq one
-- statement:
--   The Symp Mod construction uses the exists pair eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsStdSympZmod.lean#L16-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsStdSympZmod.lean#L16-L59

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

theorem GlobalTheory.SympMod.exists_pair_eq_one {M g : ℕ} [NeZero M] {V : Type*} [AddCommGroup V] [Module (ZMod M) V]
    {B : LinearMap.BilinForm (ZMod M) V} (N : Submodule (ZMod M) V)
    (hN : ∀ x ∈ N, (∀ y ∈ N, B x y = 0) → x = 0)
    (hc : ∀ d, d ∣ M → Nat.card {x : V // x ∈ N ∧ d • x = 0} = d ^ (2 * (g + 1))) :
    ∃ e ∈ N, ∃ f ∈ N, B e f = 1 := by sorry
