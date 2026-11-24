-- Prove2me | Theorems.Thm_GlobalTheory_T_squareZero_local_lifts_corrected_agree_on_overlaps
-- name    : GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:00:20.257864+00:00
-- url     : https://prove2.me/theorems/b51000f6-3605-4c6e-968d-abc595b16f5b
-- title:
--   T: square Zero local lifts corrected agree on overlaps
-- statement:
--   The T construction uses the square Zero local lifts corrected agree on overlaps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SquareZeroLocalLiftsCorrectedAgreeOnOverlapsStatement.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SquareZeroLocalLiftsCorrectedAgreeOnOverlapsStatement.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquareZeroLocalLiftsCorrectedAgreeOnOverlaps
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquareZeroLocalLiftsCorrectedAgreeOnOverlapsStatement
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

theorem GlobalTheory.T.squareZero_local_lifts_corrected_agree_on_overlaps : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (κ : Type) [Finite κ] (f : κ → R), Ideal.span (Set.range f) = ⊤ → ∀ V : κ → X.left.Opens, (∀ k, IsAffineOpen (V k)) →
    (∀ k, GlobalTheory.SecLift.LiftIn π X g₀ (f k) (V k)) →
    ∃ e : ∀ k, Sp (Localization.Away (f k)) ⟶ X.left,
      (∀ k, e k ≫ X.hom = spMap (algebraMap R (Localization.Away (f k)))) ∧
      (∀ k, spMap (Localization.awayMap π (f k)) ≫ e k = spMap (algebraMap R₀ (Localization.Away (π (f k)))) ≫ g₀) ∧
      ∀ j k, spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (f j * f k)) (f j) (f k)) ≫ e j =
        spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (f j * f k)) (f k) (f j)) ≫ e k := by sorry
