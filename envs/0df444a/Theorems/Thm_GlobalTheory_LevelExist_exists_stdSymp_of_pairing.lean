-- Prove2me | Theorems.Thm_GlobalTheory_LevelExist_exists_stdSymp_of_pairing
-- name    : GlobalTheory.LevelExist.exists_stdSymp_of_pairing
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:03:32.210535+00:00
-- url     : https://prove2.me/theorems/d22b1760-9c15-47f2-9d51-3128970fb3fb
-- title:
--   Level Exist: exists std Symp of pairing
-- statement:
--   The Level Exist construction uses the exists std Symp of pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsIsSymplecticFamilySpan.lean#L167-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/ExistsIsSymplecticFamilySpan.lean#L167-L233

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

theorem GlobalTheory.LevelExist.exists_stdSymp_of_pairing {p J g : ℕ} (hp : p.Prime) {G R : Type*} [CommGroup G] [CommRing R] [IsDomain R]
    (hc : ∀ m, Nat.card {x : G // x ^ p ^ m = 1} = (p ^ m) ^ (2 * g)) {ze : Rˣ} (hz : IsPrimitiveRoot ze (p ^ J))
    (W : G → G → Rˣ → Prop) (hW : ∀ x y, x ^ p ^ J = 1 → y ^ p ^ J = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) (halt : ∀ x, x ^ p ^ J = 1 → W x x 1)
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x, x ^ p ^ J = 1 → (∀ y, y ^ p ^ J = 1 → W x y 1) → x = 1) :
    ∃ v : Fin (2 * g) → G, (∀ i, v i ^ p ^ J = 1) ∧ (∀ i k, W (v i) (v k) (ze ^ stdSymp g i k)) ∧
      Function.Injective fun c : Fin (2 * g) → Fin (p ^ J) => ∏ i, v i ^ (c i : ℕ) := by sorry
