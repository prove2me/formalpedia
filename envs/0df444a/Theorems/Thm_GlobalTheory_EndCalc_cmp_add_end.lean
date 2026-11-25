-- Prove2me | Theorems.Thm_GlobalTheory_EndCalc_cmp_add_end
-- name    : GlobalTheory.EndCalc.cmp_add_end
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:00:53.284858+00:00
-- url     : https://prove2.me/theorems/8e1bf960-5758-4ecd-bd66-89e998cad026
-- title:
--   End Calc: cmp add end
-- statement:
--   The End Calc construction uses the cmp add end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UniformizationEndomorphismCalculus.lean#L131-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/UniformizationEndomorphismCalculus.lean#L131-L144

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DvrLem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniformizationEndomorphismOfLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsNsmulIffEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_UniformizationEndomorphismCalculus
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
open GlobalTheory GlobalTheory.EndCalc
variable {R : Type} [CommRing R] [IsDomain R]
variable {D : DegPre R} {a a' a'' : D.P.A ⟶ D.P.A} {p p' p'' χ χ' χ'' : D.X} {T : Over (Spec (CommRingCat.of R))}
  {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι}

theorem GlobalTheory.EndCalc.cmp_add_end (hG : GlobalFnsSt) [IsMonHom a] {u : CmpGen D a p χ} (hu : Normd u) {u' : CmpGen D a' p' χ}
    (hu' : Normd u') {u'' : CmpGen D a'' p'' χ} (hu'' : Normd u'') (ha : a'' = a * a') (hp : p'' = p + p')
    (hJ : Good D.P.L z J) (x : T ⟶ D.P.A) :
    val u'' x.left z J * th D z J (cP D T χ) (x ≫ a) (x ≫ a') =
      th D z J (cP D T p) (cP D T p') x * (val u x.left z J * val u' x.left z J) := by sorry
