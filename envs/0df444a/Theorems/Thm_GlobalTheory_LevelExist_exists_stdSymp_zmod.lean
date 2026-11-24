-- Prove2me | Theorems.Thm_GlobalTheory_LevelExist_exists_stdSymp_zmod
-- name    : GlobalTheory.LevelExist.exists_stdSymp_zmod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:04:07.357007+00:00
-- url     : https://prove2.me/theorems/fc9d8ef8-496c-4cad-843c-45f00b09afba
-- title:
--   Level Exist: exists std Symp zmod
-- statement:
--   The Level Exist construction uses the exists std Symp zmod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsIsSymplecticFamilySpan.lean#L101-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsIsSymplecticFamilySpan.lean#L101-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsIsSymplecticFamilySpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.LevelExist
open ReciprocityTheory.ChartRestriction.G.Out

theorem GlobalTheory.LevelExist.exists_stdSymp_zmod {p j g : ℕ} (hp : p.Prime) {V : Type*} [AddCommGroup V] [Module (ZMod (p ^ (j + 1))) V]
    (h₀ : Nat.card V = (p ^ (j + 1)) ^ (2 * g)) (h₁ : Nat.card {x : V // p ^ j • x = 0} = (p ^ j) ^ (2 * g))
    (h₂ : Nat.card {x : V // p • x = 0} = p ^ (2 * g))
    {B : LinearMap.BilinForm (ZMod (p ^ (j + 1))) V} (hB : B.IsAlt) (hN : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ v : Fin (2 * g) → V, (∀ i k, B (v i) (v k) = (stdSymp g i k : ℤ)) ∧
      LinearIndependent (ZMod (p ^ (j + 1))) v := by sorry
