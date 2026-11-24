-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_affineCombination_squareZero_lifts_cocycle
-- name    : GlobalTheory.SecGlue.Red.affineCombination_squareZero_lifts_cocycle
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:50:41.424869+00:00
-- url     : https://prove2.me/theorems/3ac9432b-823d-405c-beee-884d56406928
-- title:
--   Red: affine Combination square Zero lifts cocycle
-- statement:
--   The Red construction uses the affine Combination square Zero lifts cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L221-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L221-L281

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

theorem GlobalTheory.SecGlue.Red.affineCombination_squareZero_lifts_cocycle {R R₀ : Type} [CommRing R] [CommRing R₀] (π : R →+* R₀)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π ^ 2 = ⊥) (X : Over (Sp R))
    (g₀ : Sp R₀ ⟶ X.left) (fj fl fk : R) (Vj Vl W : X.left.Opens) (hVj : IsAffineOpen Vj)
    (hVl : IsAffineOpen Vl) (hW : IsAffineOpen W)
    (ej tj t'j : Sp (Localization.Away fj) ⟶ X.left) (el tl t'l : Sp (Localization.Away fl) ⟶ X.left)
    (rej : spMap (Localization.awayMap π fj) ≫ ej = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rtj : spMap (Localization.awayMap π fj) ≫ tj = spMap (algebraMap R₀ (Localization.Away (π fj))) ≫ g₀)
    (rel : spMap (Localization.awayMap π fl) ≫ el = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (rtl : spMap (Localization.awayMap π fl) ≫ tl = spMap (algebraMap R₀ (Localization.Away (π fl))) ≫ g₀)
    (N M M₀ : ℕ) (hM : M₀ ≤ M)
    (h'j : IsCombIn Vj ej t'j ![tj] ![algebraMap R (Localization.Away fj) fk ^ M])
    (h'l : IsCombIn Vl el t'l ![tl] ![algebraMap R (Localization.Away fl) fk ^ M])
    (S : Type) [CommRing S] [Algebra R S] (ρj : Localization.Away fj →+* S)
    (ρl : Localization.Away fl →+* S) (hρj : ρj.comp (algebraMap R _) = algebraMap R S)
    (hρl : ρl.comp (algebraMap R _) = algebraMap R S) (hA : (spMap ρj ≫ ej) ⁻¹ᵁ W = ⊤)
    (c : Sp S ⟶ X.left)
    (hc : IsCombIn W (spMap ρl ≫ el) c ![spMap ρl ≫ tl, spMap ρj ≫ ej] ![1, 1 - algebraMap R S fk ^ N])
    (hM₀ : ∀ (h₁ : (spMap ρj ≫ tj) ⁻¹ᵁ W = ⊤) (h₂ : c ⁻¹ᵁ W = ⊤) x,
      algebraMap R S fk ^ M₀ * chartHom W (spMap ρj ≫ tj) h₁ x =
        algebraMap R S fk ^ M₀ * chartHom W c h₂ x) :
    IsCombIn W (spMap ρl ≫ el) (spMap ρj ≫ t'j) ![spMap ρl ≫ t'l, spMap ρj ≫ ej]
      ![1, 1 - algebraMap R S fk ^ (N + M)] := by sorry
