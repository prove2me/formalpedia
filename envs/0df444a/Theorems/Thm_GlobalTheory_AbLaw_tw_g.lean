-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_tw_g
-- name    : GlobalTheory.AbLaw.tw_g
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:21.804323+00:00
-- url     : https://prove2.me/theorems/03365419-e9e8-4702-b45f-8b5d976977cd
-- title:
--   Ab Law: tw g
-- statement:
--   The Ab Law construction uses the tw g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/FirstCohomologyVanishesSpecOfIsLocalRing.lean#L117-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/FirstCohomologyVanishesSpecOfIsLocalRing.lean#L117-L125

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
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
variable {X X' : Scheme.{0}} {R : Type} [CommRing R]

theorem GlobalTheory.AbLaw.tw_g (M H : LB X) (t : ℤ) (p q : M.ι × H.ι) :
    (tw M H t).g p q =
      res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
        M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) ≤ M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1) *
      res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
        M.U p.1 ⊓ H.U p.2 ⊓ (M.U q.1 ⊓ H.U q.2) ≤ H.U p.2 ⊓ H.U q.2) (H.g p.2 q.2) ^ t := by sorry
