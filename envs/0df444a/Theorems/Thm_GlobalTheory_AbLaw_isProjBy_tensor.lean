-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_isProjBy_tensor
-- name    : GlobalTheory.AbLaw.isProjBy_tensor
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:43:51.238048+00:00
-- url     : https://prove2.me/theorems/0b4e8ab1-7e0d-4ae7-826d-c9514d7ce93a
-- title:
--   Ab Law: is Proj By tensor
-- statement:
--   The Ab Law construction uses the is Proj By tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L200-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L200-L202

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

theorem GlobalTheory.AbLaw.isProjBy_tensor : ∀ (R : Type) [CommRing R] (X Y : Over (Spec (CommRingCat.of R))),
    IsProjBy X.hom → IsProjBy Y.hom → IsProjBy (X ⊗ Y).hom := by sorry
