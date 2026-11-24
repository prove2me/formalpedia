-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_H1Iso_firstCohomologyVanishes_of_iso_of_isGen
-- name    : GlobalTheory.AbLaw.H1Iso.firstCohomologyVanishes_of_iso_of_isGen
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:52:32.702654+00:00
-- url     : https://prove2.me/theorems/6f38829f-6f00-4330-844b-de7bec865d6b
-- title:
--   H1 Iso: first Cohomology Vanishes of iso of is Gen
-- statement:
--   The H1 Iso construction uses the first Cohomology Vanishes of iso of is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L129-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FirstCohomologyVanishesOfIsoOfIsGen.lean#L129-L212

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

theorem GlobalTheory.AbLaw.H1Iso.firstCohomologyVanishes_of_iso_of_isGen {N M : LB X} (hN : ⨆ i, N.U i = ⊤) (hM : M.IsLB) (w : LB.Iso M N)
    (hw : w.IsGen) (h0 : FirstCohomologyVanishes N) : FirstCohomologyVanishes M := by sorry
