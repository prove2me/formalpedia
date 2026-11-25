-- Prove2me | Theorems.Thm_GlobalTheory_TorusCoordPull_weight_pull
-- name    : GlobalTheory.TorusCoordPull.weight_pull
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:23.339635+00:00
-- url     : https://prove2.me/theorems/2c2e342f-c22e-444a-825b-e1c4d330a4d2
-- title:
--   Torus Coord Pull: weight pull
-- statement:
--   The Torus Coord Pull construction uses the weight pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGrpPullbackThick.lean#L285-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGrpPullbackThick.lean#L285-L331

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
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {S S' : Scheme.{0}} {j : S ⟶ Spec (CommRingCat.of R)}
  {j' : S' ⟶ Spec (CommRingCat.of R')} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'} [GrpObj G']
  [IsCommMonObj G'] (p : (Over.map j).obj G ⟶ D.P.A) (p' : (Over.map j').obj G' ⟶ D'.P.A) (h : G'.left ⟶ G.left)
  (hp : p'.left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) = h ≫ p.left)
  {σ : S' ⟶ S} (gp : IsGrpPullback G' G σ h) {χ : D'.X}
  {t : LB.Gen (LB.LinComb D.P.L (D.Oφ p (hD.xe χ)) Oinvε)} {a : LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' χ) Oinvε)}
  (H : PMaps hD.w (D'.Oφ p' χ) (D.Oφ p (hD.xe χ)) Oinvε a t h)
omit [IsCommMonObj G] [IsCommMonObj G']
include hp gp H

theorem GlobalTheory.TorusCoordPull.weight_pull (i : splitTorus S D.X ⟶ G) (i' : splitTorus S' D'.X ⟶ G')
    (hT : (splitTorus S' D'.X).left ⟶ (splitTorus S D.X).left) (hi : i'.left ≫ h = hT ≫ i.left)
    (hχ : hT.appTop.hom (charUnit _ D.X (hD.xe χ)).val = (charUnit _ D'.X χ).val)
    (aO : (Over.map j').map (lift (fst (splitTorus S' D'.X) G' ≫ i') (snd _ _) ≫ μ[G']) ≫ p' =
      (Over.map j').map (snd (splitTorus S' D'.X) G') ≫ p')
    (hw : LB.Gen.Corr D.P.L _ _ _ _
      (LB.pullGen D.P.L _ _ t (lift (fst (splitTorus S D.X) G ≫ i) (snd _ _) ≫ μ[G]).left)
      (LB.mulGen D.P.L _ _ _ _ (charGen D.X G D.P.L (hD.xe χ))
        (LB.pullGen D.P.L _ _ t (snd (splitTorus S D.X) G).left))) :
    LB.Gen.Corr D'.P.L _ _ _ _
      (LB.pullGen D'.P.L _ _ a (lift (fst (splitTorus S' D'.X) G' ≫ i') (snd _ _) ≫ μ[G']).left)
      (LB.mulGen D'.P.L _ _ _ _ (charGen D'.X G' D'.P.L χ)
        (LB.pullGen D'.P.L _ _ a (snd (splitTorus S' D'.X) G').left)) := by sorry
