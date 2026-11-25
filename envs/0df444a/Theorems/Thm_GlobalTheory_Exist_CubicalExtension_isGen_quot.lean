-- Prove2me | Theorems.Thm_GlobalTheory_Exist_CubicalExtension_isGen_quot
-- name    : GlobalTheory.Exist.CubicalExtension.isGen_quot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:44:40.041247+00:00
-- url     : https://prove2.me/theorems/1d898a24-72e9-5d93-9949-0892725b6881
-- title:
--   Cubical Extension: is Gen quot
-- statement:
--   The Cubical Extension construction uses the is Gen quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SabMapOfIsoOfExtendGen.lean#L40-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/SabMapOfIsoOfExtendGen.lean#L40-L49

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

theorem GlobalTheory.Exist.CubicalExtension.isGen_quot {j : A ⟶ X'} (s : ∀ a i, Γ(A, qchart L L' F j a i)ˣ)
    (h : ∀ (y : A) a a' i i', F (j y) ∈ L.U a → F (j y) ∈ L.U a' → j y ∈ L'.U i → j y ∈ L'.U i' →
      gm (𝟙 A) y _ (s a i) = gm (j ≫ F) y _ (L.g a a') * (gm j y _ (L'.g i i'))⁻¹ * gm (𝟙 A) y _ (s a' i')) :
    LB.Gen.IsGen (L := (LB.div (L.pull F) L').pull j) ⟨fun J => s ((J PUnit.unit).1 PUnit.unit) (J PUnit.unit).2⟩ := by sorry
