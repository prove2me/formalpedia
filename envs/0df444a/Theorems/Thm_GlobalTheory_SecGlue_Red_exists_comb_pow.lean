-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_exists_comb_pow
-- name    : GlobalTheory.SecGlue.Red.exists_comb_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:49:21.975532+00:00
-- url     : https://prove2.me/theorems/5322fb6b-e956-4b61-8360-f2eb5d5bfd93
-- title:
--   Red: exists comb pow
-- statement:
--   The Red construction uses the exists comb pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L91-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L91-L215

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgHomEqMulPowOfEqLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowCocycle
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
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
open IsLocalization.Away

theorem GlobalTheory.SecGlue.Red.exists_comb_pow {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = ⊥) (X : Over (Sp R)) (hsm : Smooth X.hom)
    (g₀ : Sp R₀ ⟶ X.left) (fj fl fk : R) (Vj Vl W : X.left.Opens) (hVj : IsAffineOpen Vj)
    (hVl : IsAffineOpen Vl) (hW : IsAffineOpen W)
    (ej tj : Sp (Localization.Away fj) ⟶ X.left) (el tl : Sp (Localization.Away fl) ⟶ X.left)
    (ek : Sp (Localization.Away fk) ⟶ X.left)
    (hej : ej ≫ X.hom = spMap (algebraMap R _)) (htj : tj ≫ X.hom = spMap (algebraMap R _))
    (hel : el ≫ X.hom = spMap (algebraMap R _)) (htl : tl ≫ X.hom = spMap (algebraMap R _))
    (rej : spMap (Localization.awayMap π fj) ≫ ej = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rtj : spMap (Localization.awayMap π fj) ≫ tj = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rel : spMap (Localization.awayMap π fl) ≫ el = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (rtl : spMap (Localization.awayMap π fl) ≫ tl = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (rek : spMap (Localization.awayMap π fk) ≫ ek = spMap (algebraMap R₀ (Localization.Away (π fk))) ≫ g₀)
    (N : ℕ)
    (hcj : IsCombIn Vj (spMap (awayToAwayRight (P := Localization.Away (fj * fk)) fj fk) ≫ ej)
      (spMap (awayToAwayRight (P := Localization.Away (fj * fk)) fj fk) ≫ tj)
      ![spMap (awayToAwayLeft (P := Localization.Away (fj * fk)) fk fj) ≫ ek]
      ![algebraMap R (Localization.Away (fj * fk)) fk ^ N])
    (hcl : IsCombIn Vl (spMap (awayToAwayRight (P := Localization.Away (fl * fk)) fl fk) ≫ el)
      (spMap (awayToAwayRight (P := Localization.Away (fl * fk)) fl fk) ≫ tl)
      ![spMap (awayToAwayLeft (P := Localization.Away (fl * fk)) fk fl) ≫ ek]
      ![algebraMap R (Localization.Away (fl * fk)) fk ^ N])
    (S : Type) [CommRing S] [Algebra R S] (ρj : Localization.Away fj →+* S)
    (ρl : Localization.Away fl →+* S) (hρj : ρj.comp (algebraMap R _) = algebraMap R S)
    (hρl : ρl.comp (algebraMap R _) = algebraMap R S) (hA : (spMap ρj ≫ ej) ⁻¹ᵁ W = ⊤) :
    ∃ c : Sp S ⟶ X.left, IsCombIn W (spMap ρl ≫ el) c ![spMap ρl ≫ tl, spMap ρj ≫ ej]
        ![1, 1 - algebraMap R S fk ^ N] ∧
      ∃ M₀ : ℕ, ∀ (h₁ : (spMap ρj ≫ tj) ⁻¹ᵁ W = ⊤) (h₂ : c ⁻¹ᵁ W = ⊤) x,
        algebraMap R S fk ^ M₀ * chartHom W (spMap ρj ≫ tj) h₁ x =
          algebraMap R S fk ^ M₀ * chartHom W c h₂ x := by sorry
