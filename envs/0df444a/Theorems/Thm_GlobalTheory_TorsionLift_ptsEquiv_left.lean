-- Prove2me | Theorems.Thm_GlobalTheory_TorsionLift_ptsEquiv_left
-- name    : GlobalTheory.TorsionLift.ptsEquiv_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:03:23.767217+00:00
-- url     : https://prove2.me/theorems/593d1d8e-08ec-4049-b25a-1f1d8b1d16ac
-- title:
--   Torsion Lift: pts Equiv left
-- statement:
--   The Torsion Lift construction uses the pts Equiv left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueOfIsAdicComplete.lean#L224-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniqueOfIsAdicComplete.lean#L224-L228

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ReductionSurjectiveOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteOfIsClosedSplitTorusOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueOfIsAdicComplete
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp spMap_id)
open IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorsionLift
variable {R : Type} [CommRing R] [IsLocalRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
  [IsCommMonObj G] [Smooth G.hom]

theorem GlobalTheory.TorsionLift.ptsEquiv_left {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] (T : Over S')
    (t : T.left ⟶ S) (ht : T.hom ≫ p = t) (x : T ⟶ (Over.pullback p).obj G) :
    (ptsEquiv p G T t ht x).left = x.left ≫ pullback.fst G.hom p := by sorry
