-- Prove2me | Theorems.Thm_GlobalTheory_TorusCoordPull_val_unit_pull
-- name    : GlobalTheory.TorusCoordPull.val_unit_pull
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:53.242574+00:00
-- url     : https://prove2.me/theorems/1c0a4a43-b2fc-402f-87f0-6138d782f768
-- title:
--   Torus Coord Pull: val unit pull
-- statement:
--   The Torus Coord Pull construction uses the val unit pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGrpPullbackThick.lean#L190-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGrpPullbackThick.lean#L190-L197

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGrpPullbackThick
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.TorusCoordPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR TopologicalSpace
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}
variable (hD : IsPullDeg φ D D') {T : Over (Spec (CommRingCat.of R))} {T' : Over (Spec (CommRingCat.of R'))}
  (p : T ⟶ D.P.A) (p' : T' ⟶ D'.P.A) (h : T'.left ⟶ T.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)
include hp

theorem GlobalTheory.TorusCoordPull.val_unit_pull {x : D'.X} {t : LB.Gen (LB.LinComb D.P.L (D.Oφ p (hD.xe x)) Oinvε)}
    {a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' x) Oinvε)}
    (H : PMaps hD.w (D'.Oφ p' x) (D.Oφ p (hD.xe x)) Oinvε a t h) {T₀ : Over (Spec (CommRingCat.of R'))}
    (ρ : T₀ ⟶ T') (hρ : ρ ≫ p' = 1) {y : T₀.left} {J J'} (hJ : Good D.P.L y J) (hJ' : Good D'.P.L y J') :
    val t (ρ.left ≫ h) y J = val a ρ.left y J' := by sorry
