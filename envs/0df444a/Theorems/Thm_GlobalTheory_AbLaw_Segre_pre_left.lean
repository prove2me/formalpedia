-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Segre_pre_left
-- name    : GlobalTheory.AbLaw.Segre.pre_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:52:41.330413+00:00
-- url     : https://prove2.me/theorems/5346dc8c-f870-497b-9dd2-2c6f6c022db2
-- title:
--   Segre: pre left
-- statement:
--   The Segre construction uses the pre left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L39-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsProjByOfIsPullback.lean#L39-L40

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

theorem GlobalTheory.AbLaw.Segre.pre_left (p : P ⟶ X) {U V : X.Opens} {W : P.Opens} (h : W ≤ p ⁻¹ᵁ (U ⊓ V)) :
    W ≤ p ⁻¹ᵁ U := by sorry
