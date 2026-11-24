-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Segre_pre_right
-- name    : GlobalTheory.AbLaw.Segre.pre_right
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:51:49.648807+00:00
-- url     : https://prove2.me/theorems/5fb40152-d383-4dd1-80d3-7611fa0907e6
-- title:
--   Segre: pre right
-- statement:
--   The Segre construction uses the pre right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L42-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L42-L43

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

theorem GlobalTheory.AbLaw.Segre.pre_right (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (U ⊓ V)) :
    W ≤ p ⁻¹ᵁ V := by sorry
