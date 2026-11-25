-- Prove2me | Theorems.Thm_GlobalTheory_GenericFibreSections_gw_trans
-- name    : GlobalTheory.GenericFibreSections.gw_trans
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:05.67553+00:00
-- url     : https://prove2.me/theorems/89169dca-33e8-4bb4-ba62-e8fdc89ecd83
-- title:
--   Generic Fibre Sections: gw trans
-- statement:
--   The Generic Fibre Sections construction uses the gw trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BijectiveOfIso.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/BijectiveOfIso.lean#L92-L98

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_BijectiveOfIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.GenericFibreSections
variable {X₁ X₂ Y Y' : Scheme.{0}} {L₁ : LB X₁} {L₂ : LB X₂}

theorem GlobalTheory.GenericFibreSections.gw_trans {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)} (hw : w.IsGen) (y : Y)
    {i i' : L₁.ι} {j j' : L₂.ι} (hi : f₁ y ∈ L₁.U i) (hi' : f₁ y ∈ L₁.U i') (hj : f₂ y ∈ L₂.U j) (hj' : f₂ y ∈ L₂.U j') :
    gw w (𝟙 Y) y j (fun _ => i) * gm (𝟙 Y ≫ f₁) y _ (L₁.g i i') =
      gm (𝟙 Y ≫ f₂) y _ (L₂.g j j') * gw w (𝟙 Y) y j' (fun _ => i') := by sorry
