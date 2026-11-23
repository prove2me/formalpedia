-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_compat_at
-- name    : GlobalTheory.SecGlue.compat_at
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:53:15.183051+00:00
-- url     : https://prove2.me/theorems/b99938df-ebf8-443a-a251-5e7587bbc63d
-- title:
--   Sec Glue: compat at
-- statement:
--   The Sec Glue construction uses the compat at property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueSectionsPrincipalCover.lean#L105-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueSectionsPrincipalCover.lean#L105-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {A X Y Z : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {ε : K → ℤ}

theorem GlobalTheory.SecGlue.compat_at {φ : K → (X ⟶ A)} (r : Z ⟶ X) (z : Z) {j j' : K → L.ι}
    (f : Γ(X, LB.wchart L φ j)) (f' : Γ(X, LB.wchart L φ j'))
    (hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j')
    (h : gs r z _ f = (trF φ ε r z j j').val * gs r z _ f') :
    gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((X.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j') (((LB.LinComb L φ ε).g j j').val *
        (X.presheaf.map (homOfLE inf_le_right).op).hom f') := by sorry
