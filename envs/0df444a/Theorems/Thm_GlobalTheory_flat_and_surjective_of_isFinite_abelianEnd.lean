-- Prove2me | Theorems.Thm_GlobalTheory_flat_and_surjective_of_isFinite_abelianEnd
-- name    : GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:00.393296+00:00
-- url     : https://prove2.me/theorems/c9c334e6-c9eb-429e-a20f-a9d0bdfd47f4
-- title:
--   Global Theory: flat and surjective of is Finite abelian End
-- statement:
--   The Global Theory construction uses the flat and surjective of is Finite abelian End property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatAndSurjectiveOfIsFiniteAbelianEnd.lean#L139-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatAndSurjectiveOfIsFiniteAbelianEnd.lean#L139-L149

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S),
      Smooth f → GeometricallyConnected f → GeometricallyIntegral f) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A],
      IsAbelianScheme A → ∀ f : A ⟶ A, IsMonHom f → IsFinite f.left →
        Flat f.left ∧ Surjective f.left := by sorry
