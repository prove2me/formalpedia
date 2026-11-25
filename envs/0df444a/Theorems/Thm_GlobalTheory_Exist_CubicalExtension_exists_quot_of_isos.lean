-- Prove2me | Theorems.Thm_GlobalTheory_Exist_CubicalExtension_exists_quot_of_isos
-- name    : GlobalTheory.Exist.CubicalExtension.exists_quot_of_isos
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:34.249311+00:00
-- url     : https://prove2.me/theorems/0ad7cc4e-9f8c-5c6b-9c95-81726458ce88
-- title:
--   Cubical Extension: exists quot of isos
-- statement:
--   The Cubical Extension construction uses the exists quot of isos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SabMapOfIsoOfExtendGen.lean#L51-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SabMapOfIsoOfExtendGen.lean#L51-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SabMapOfIsoOfExtendGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Exist GlobalTheory.Exist.CubicalExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' X'' A : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X} {F' : X'' ⟶ X'}

theorem GlobalTheory.Exist.CubicalExtension.exists_quot_of_isos (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB) (w' : LB.Iso L'' (L'.pull F'))
    (w'' : LB.Iso L'' (L.pull (F' ≫ F))) (hw' : PGen w') (hw'' : PGen w'') (κ : A ⟶ X'') (j : A ⟶ X')
    (hj : κ ≫ F' = j) :
    ∃ r : LB.Gen ((LB.div (L.pull F) L').pull j), r.IsGen ∧
      ∀ (Y : Scheme.{0}) (f : Y ⟶ A) (y : Y) a i k, F (j (f y)) ∈ L.U a → j (f y) ∈ L'.U i → κ (f y) ∈ L''.U k →
        gm f y (qchart L L' F j a i) (r.s (fun _ => (fun _ => a, i))) =
          gw w'' (f ≫ κ) y a k * (gw w' (f ≫ κ) y i k)⁻¹ := by sorry
