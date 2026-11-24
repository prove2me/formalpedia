-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_H1Iso_iso_rel
-- name    : GlobalTheory.AbLaw.H1Iso.iso_rel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:52:56.01537+00:00
-- url     : https://prove2.me/theorems/acce5c18-d8f8-45a5-a10f-622d8677878e
-- title:
--   H1 Iso: iso rel
-- statement:
--   The H1 Iso construction uses the iso rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L100-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L100-L117

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

theorem GlobalTheory.AbLaw.H1Iso.iso_rel {N M : LB X} (w : LB.Iso M N) (hw : w.IsGen) (i j : N.ι) (k l : M.ι) {W : X.Opens}
    (hi : W ≤ N.U i) (hj : W ≤ N.U j) (hk : W ≤ M.U k) (hl : W ≤ M.U l) :
    rs X (le_inf hi hk : W ≤ N.U i ⊓ M.U k) (wu w i k).val *
        rs X (le_inf hk hl : W ≤ M.U k ⊓ M.U l) (M.g k l).val =
      rs X (le_inf hi hj : W ≤ N.U i ⊓ N.U j) (N.g i j).val *
        rs X (le_inf hj hl : W ≤ N.U j ⊓ M.U l) (wu w j l).val := by sorry
