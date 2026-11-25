-- Prove2me | Theorems.Thm_GlobalTheory_groupRing_hom_const_of_laurent
-- name    : GlobalTheory.groupRing_hom_const_of_laurent
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:28:59.8974+00:00
-- url     : https://prove2.me/theorems/2fc8c4e9-245f-4c12-9e4e-bec4f80ca9fd
-- title:
--   Global Theory: group Ring hom const of laurent
-- statement:
--   The Global Theory construction uses the group Ring hom const of laurent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GroupRingHomConstOfLaurent.lean#L167-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/GroupRingHomConstOfLaurent.lean#L167-L192

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.GroupRingConst

theorem GlobalTheory.groupRing_hom_const_of_laurent {S Y : Scheme.{0}} (p : Y ⟶ S) [IsSeparated p]
    (h : ∀ (L : Type) [Field L] (s : Spec (CommRingCat.of L) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra L ℤ)) ⟶ Y),
      f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ s →
      ∃ k : Spec (CommRingCat.of L) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap L (AddMonoidAlgebra L ℤ))) ≫ k)
    (R : Type) [CommRing R] [IsDomain R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (s : Spec (CommRingCat.of R) ⟶ S) (f : Spec (CommRingCat.of (AddMonoidAlgebra R X)) ⟶ Y)
    (hf : f ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ s) :
    ∃ k : Spec (CommRingCat.of R) ⟶ Y, f = Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R X))) ≫ k := by sorry
