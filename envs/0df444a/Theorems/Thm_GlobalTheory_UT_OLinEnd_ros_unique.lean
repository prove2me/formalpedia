-- Prove2me | Theorems.Thm_GlobalTheory_UT_OLinEnd_ros_unique
-- name    : GlobalTheory.UT.OLinEnd.ros_unique
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:12:56.878371+00:00
-- url     : https://prove2.me/theorems/ef0dbdfa-fed3-59e3-be63-378b9f119e62
-- title:
--   OLin End: ros unique
-- statement:
--   The OLin End construction uses the ros unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniformizationEndomorphismOfLinear.lean#L76-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsUniformizationEndomorphismOfLinear.lean#L76-L89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
noncomputable section
open GlobalTheory GlobalTheory.UT GlobalTheory.UT.OLinEnd
variable {R : Type} [CommRing R] [IsDomain R]

theorem GlobalTheory.UT.OLinEnd.ros_unique (hG : GlobalFnsSt) (D : DegPre R) {f g : D.P.A ⟶ D.P.A}
    {u u' : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (u₀' : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u' (zero2 D.P.A)) (LB.oneGen D.P.L))
    (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D.P.A).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    val u' r z J = val u r z J := by sorry
