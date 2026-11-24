-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Segre_ap_cocycle
-- name    : GlobalTheory.AbLaw.Segre.ap_cocycle
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:51:52.471228+00:00
-- url     : https://prove2.me/theorems/87a3c8a1-bcff-49a3-890a-6dd34d243314
-- title:
--   Segre: ap cocycle
-- statement:
--   The Segre construction uses the ap cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L64-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L64-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsProjByOfIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Segre
variable {X Y P : Scheme.{0}} {R : Type} [CommRing R]
variable (p : P ⟶ X) (q : P ⟶ Y) {H : LB X} {K : LB Y}

theorem GlobalTheory.AbLaw.Segre.ap_cocycle (hH : H.IsLB) (i j k : H.ι) {W : P.Opens} (h₁ : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U j))
    (h₂ : W ≤ p ⁻¹ᵁ (H.U j ⊓ H.U k)) (h₃ : W ≤ p ⁻¹ᵁ (H.U i ⊓ H.U k)) :
    ap p h₃ (H.g i k).val = ap p h₁ (H.g i j).val * ap p h₂ (H.g j k).val := by sorry
