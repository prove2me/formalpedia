-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_chartHom_pow_mul_eq
-- name    : GlobalTheory.SecGlue.Red.chartHom_pow_mul_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:49:33.630683+00:00
-- url     : https://prove2.me/theorems/8792b991-01b2-4564-856b-b2d7351b499e
-- title:
--   Red: chart Hom pow mul eq
-- statement:
--   The Red construction uses the chart Hom pow mul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L16-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L16-L45

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

theorem GlobalTheory.SecGlue.Red.chartHom_pow_mul_eq {R : Type} [CommRing R] (X : Over (Sp R)) (hsm : Smooth X.hom)
    (W : X.left.Opens) (hW : IsAffineOpen W) {S : Type} [CommRing S] (u₁ u₂ : Sp S ⟶ X.left)
    (hu : u₁ ≫ X.hom = u₂ ≫ X.hom) (h₁ : u₁ ⁻¹ᵁ W = ⊤) (h₂ : u₂ ⁻¹ᵁ W = ⊤) (g : S)
    (hg : ∀ x, algebraMap S (Localization.Away g) (chartHom W u₁ h₁ x) =
      algebraMap S (Localization.Away g) (chartHom W u₂ h₂ x)) :
    ∃ M : ℕ, ∀ x, g ^ M * chartHom W u₁ h₁ x = g ^ M * chartHom W u₂ h₂ x := by sorry
