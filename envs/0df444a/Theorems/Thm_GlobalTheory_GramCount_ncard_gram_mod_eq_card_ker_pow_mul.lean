-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ncard_gram_mod_eq_card_ker_pow_mul
-- name    : GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:27:41.386191+00:00
-- url     : https://prove2.me/theorems/540bb698-8d75-53ab-b287-3afa8bbf8eb9
-- title:
--   Gram Count: ncard gram mod eq card ker pow mul
-- statement:
--   The Gram Count construction uses the ncard gram mod eq card ker pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesGramModNilpotent.lean#L34-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NcardPrimitiveTuplesGramModNilpotent.lean#L34-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NcardPrimitiveTuplesGramModNilpotent
import Theorems.Thm_GlobalTheory_GramCount_Prim_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Classical
open GlobalTheory GlobalTheory.GramCount

theorem GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul {A B : Type} [CommRing A] [Finite A] [CommRing B]
    (c : A →+* A) (c' : B →+* B) (hc : ∀ u, c (c u) = u) (p : A) (hp : IsNilpotent p)
    (φ : A →+* B) (hs : Function.Surjective φ) (hφ : ∀ u, φ (c u) = c' (φ u))
    (hk : ∀ u, φ u = 0 ↔ p ∣ u) (m n : ℕ) (G : Matrix (Fin m) (Fin m) A) :
    Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} =
      Nat.card {u : A // p ∣ u} ^ (n * m) * Set.ncard (sols c' n (G.map φ)) := by sorry
