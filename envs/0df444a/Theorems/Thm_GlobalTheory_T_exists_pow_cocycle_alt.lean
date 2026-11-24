-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_pow_cocycle_alt
-- name    : GlobalTheory.T.exists_pow_cocycle_alt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:12.916815+00:00
-- url     : https://prove2.me/theorems/23d6482e-c964-4cfc-8622-4acc860033ea
-- title:
--   T: exists pow cocycle alt
-- statement:
--   The T construction uses the exists pow cocycle alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycleStatement.lean#L7-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycleStatement.lean#L7-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowCocycle
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowCocycleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_pow_cocycle_alt : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Fintype κ] (f : κ → R), ∀ (V : κ → X.left.Opens), (∀ k, IsAffineOpen (V k)) →
    ∀ (e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left),
    (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) →
    (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) →
    (∀ k, e k ⁻¹ᵁ V k = ⊤) →
    ∀ (N : ℕ) (t : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
    (∀ k j, t k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) →
    (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) →
    (∀ k j, t k j ⁻¹ᵁ V j = ⊤) →
    (∀ k j, GlobalTheory.SecGlue.IsCombIn (V j) (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j) (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ t k j)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k] ![algebraMap R (Localization.Away (f j * f k)) (f k) ^ N]) →
    ∀ (n : κ → κ → ℕ) (s : ∀ j l, Fin (n j l) → Localization.Away (f j * f l)) (W : ∀ j l, Fin (n j l) → X.left.Opens),
    (∀ j l, Ideal.span (Set.range (s j l)) = ⊤) → (∀ j l i, IsAffineOpen (W j l i)) →
    (∀ j l i, (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j) ⁻¹ᵁ W j l i = ⊤) →
    ∃ (M : ℕ) (t' : κ → ∀ j, Sp (Localization.Away (f j)) ⟶ X.left),
      (∀ k j, t' k j ≫ X.hom = spMap (algebraMap R (Localization.Away (f j)))) ∧
      (∀ k j, spMap (Localization.awayMap π (f j)) ≫ t' k j = spMap (algebraMap R₀ (Localization.Away (π (f j)))) ≫ g₀) ∧
      (∀ k j, t' k j ⁻¹ᵁ V j = ⊤) ∧
      ∀ j l k i, GlobalTheory.SecGlue.IsCombIn (W j l i) (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ e l)
        (spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ t' k j)
        ![spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f l)) (f l) (f j)) ≫ t' k l, spMap (algebraMap (Localization.Away (f j * f l)) (Localization.Away (s j l i))) ≫ spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f l)) (f j) (f l)) ≫ e j]
        ![1, 1 - algebraMap R (Localization.Away (s j l i)) (f k) ^ (N + M)] := by sorry
