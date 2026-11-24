-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_exists_pair_lift_comb
-- name    : GlobalTheory.SecGlue.exists_pair_lift_comb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:49:28.608089+00:00
-- url     : https://prove2.me/theorems/ddb820dc-9b90-40dc-b534-e6da65a21ac4
-- title:
--   Sec Glue: exists pair lift comb
-- statement:
--   The Sec Glue construction uses the exists pair lift comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L145-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L145-L241

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue
open GlobalTheory.SecGlue.Pair
set_option maxHeartbeats 1000000

theorem GlobalTheory.SecGlue.exists_pair_lift_comb : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ (a b : R) (V : X.left.Opens), IsAffineOpen V →
    ∀ (ea : Sp (Localization.Away a) ⟶ X.left), ea ≫ X.hom = spMap (algebraMap R (Localization.Away a)) →
      spMap (Localization.awayMap π a) ≫ ea = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ → ea ⁻¹ᵁ V = ⊤ →
    ∀ (eb : Sp (Localization.Away b) ⟶ X.left), eb ≫ X.hom = spMap (algebraMap R (Localization.Away b)) →
      spMap (Localization.awayMap π b) ≫ eb = spMap (algebraMap R₀ (Localization.Away (π b))) ≫ g₀ →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ t : Sp (Localization.Away a) ⟶ X.left,
      t ≫ X.hom = spMap (algebraMap R (Localization.Away a)) ∧
      spMap (Localization.awayMap π a) ≫ t = spMap (algebraMap R₀ (Localization.Away (π a))) ≫ g₀ ∧ t ⁻¹ᵁ V = ⊤ ∧
      GlobalTheory.SecGlue.IsCombIn V
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ ea)
        (spMap (IsLocalization.Away.awayToAwayRight (P := Localization.Away (a * b)) a b) ≫ t)
        ![spMap (IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a * b)) b a) ≫ eb]
        ![algebraMap R (Localization.Away (a * b)) b ^ N] := by sorry
