-- Prove2me | Theorems.Thm_GlobalTheory_ZM_RepBC_pullpull_g
-- name    : GlobalTheory.ZM.RepBC.pullpull_g
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T14:19:46.284214+00:00
-- url     : https://prove2.me/theorems/f49ca00f-7207-48aa-8414-fabb733aa810
-- title:
--   Rep BC: pullpull g
-- statement:
--   The Rep BC construction uses the pullpull g property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ProjectiveRepresentationPullbackCoordinates.lean#L79-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ProjectiveRepresentationPullbackCoordinates.lean#L79-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ProjectiveRepresentationPullbackCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.RepBC
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.ZM.RepBC.pullpull_g (M : LB X) (π : Y ⟶ X) (x : Z ⟶ Y) (J J' : PUnit → PUnit → M.ι)
    (e : ((M.pull π).pull x).U J ⊓ ((M.pull π).pull x).U J' ≤
      (x ≫ π) ⁻¹ᵁ (M.U (J PUnit.unit PUnit.unit) ⊓ M.U (J' PUnit.unit PUnit.unit))) :
    (((M.pull π).pull x).g J J').val =
      ((x ≫ π).appLE _ _ e).hom (M.g (J PUnit.unit PUnit.unit) (J' PUnit.unit PUnit.unit)).val := by sorry
