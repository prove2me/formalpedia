-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_H1Iso_pull_g
-- name    : GlobalTheory.AbLaw.H1Iso.pull_g
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:52:22.006119+00:00
-- url     : https://prove2.me/theorems/850d99a0-0644-49ba-ac08-56c92e4fe525
-- title:
--   H1 Iso: pull g
-- statement:
--   The H1 Iso construction uses the pull g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L56-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L56-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FirstCohomologyVanishesOfIsoOfIsGen
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
noncomputable section
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory.AbLaw.H1Iso
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.AbLaw.H1Iso.pull_g (M : LB X) (e : Y ⟶ X) (j j' : (M.pull e).ι) :
    ((M.pull e).g j j').val =
      pb e (le_pre_inf e (inf_le_left.trans (pull_U_le M e j)) (inf_le_right.trans (pull_U_le M e j')) :
        (M.pull e).U j ⊓ (M.pull e).U j' ≤ e ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit)))
        (M.g (j PUnit.unit) (j' PUnit.unit)).val := by sorry
