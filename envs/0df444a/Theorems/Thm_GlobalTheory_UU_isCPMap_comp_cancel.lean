-- Prove2me | Theorems.Thm_GlobalTheory_UU_isCPMap_comp_cancel
-- name    : GlobalTheory.UU.isCPMap_comp_cancel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:19:57.735799+00:00
-- url     : https://prove2.me/theorems/485f8849-1e31-58e8-b8c0-9e60c2808147
-- title:
--   UU: is CPMap comp cancel
-- statement:
--   The UU construction uses the is CPMap comp cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapCompCancel.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsCPMapCompCancel.lean#L79-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapCompCancel
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
open GlobalTheory GlobalTheory.UU
variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [IsCommMonObj G] [GrpObj G']
  [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
  {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}

theorem GlobalTheory.UU.isCPMap_comp_cancel :
    (∀ (S S' S'' : Scheme.{0}) (f : S' ⟶ S) (f' : S'' ⟶ S') (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (G'' : Over S'') [GrpObj G''] [IsCommMonObj G''] (P : CP G) (P' : CP G') (P'' : CP G'') (F : G'.left ⟶ G.left) (hw) (w) (F' : G''.left ⟶ G'.left) (hw' : F' ≫ G'.hom = G''.hom ≫ f') (hw'' : (F' ≫ F) ≫ G.hom = G''.hom ≫ f' ≫ f), IsCPMap P' P f F hw w → (∀ w', IsCPMap P'' P' f' F' hw' w' → ∃ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' ∧ Tri w w' w'') ∧ ((∀ (T : Over S'') (x y : T ⟶ G''), toBase hw' (x * y) = toBase hw' x * toBase hw' y) → ∀ w'', IsCPMap P'' P (f' ≫ f) (F' ≫ F) hw'' w'' → ∃ w', IsCPMap P'' P' f' F' hw' w' ∧ Tri w w' w'')) := by sorry
