-- Prove2me | Theorems.Thm_GlobalTheory_exists_isMonHom_splitTorus_of_sq_eq_bot
-- name    : GlobalTheory.exists_isMonHom_splitTorus_of_sq_eq_bot
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:44:05.146013+00:00
-- url     : https://prove2.me/theorems/01ce3475-65d8-4b21-af28-124d282d6f59
-- title:
--   Global Theory: exists is Mon Hom split Torus of sq eq bot
-- statement:
--   The Global Theory construction uses the exists is Mon Hom split Torus of sq eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIsMonHomSplitTorusOfSqEqBot.lean#L324-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsIsMonHomSplitTorusOfSqEqBot.lean#L324-L403

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LeftEqIffLieVecSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsUnitAddMonoidAlgebraIffOfTwoUniqueSums
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isMonHom_of_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (epsR IsLieBasis isMonHom_of_mul)
open scoped CategoryTheory.Obj
open AddMonoidAlgebra (single mapDomainAlgHom)
open GlobalTheory
open SqZero TorusDefect
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.exists_isMonHom_splitTorus_of_sq_eq_bot (A : Type) [CommRing A] [IsLocalRing A]
    (J : Ideal A) (hJ : J ^ 2 = ⊥) (X : Type) [AddCommGroup X]
    (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G)
    (hf : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f)) :
    ∃ f' : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom f' ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f' =
        (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f := by sorry
