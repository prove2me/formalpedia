-- Prove2me | Theorems.Thm_GlobalTheory_TorusCoordPull_mul_pull
-- name    : GlobalTheory.TorusCoordPull.mul_pull
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:10:08.99396+00:00
-- url     : https://prove2.me/theorems/79e95996-9605-46cd-a843-6edcb19442a2
-- title:
--   Torus Coord Pull: mul pull
-- statement:
--   The Torus Coord Pull construction uses the mul pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGrpPullbackThick.lean#L136-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsGrpPullbackThick.lean#L136-L187

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

theorem GlobalTheory.TorusCoordPull.mul_pull (hG : GlobalFnsSt) (t : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (D.Oφ p χ) Oinvε))
    (a : ∀ χ : D'.X, LB.Gen (LB.LinComb D'.P.L (D'.Oφ p' χ) Oinvε))
    (H : ∀ x, PMaps hD.w (D'.Oφ p' x) (D.Oφ p (hD.xe x)) Oinvε (a x) (t (hD.xe x)) h)
    (hm : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (t (χ + χ'))
        (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
          (lift (toUnit _ ≫ D.c χ) (lift (toUnit _ ≫ D.c χ') p)).left))
      (LB.mulGen D.P.L _ _ _ _ (t χ) (t χ'))) (χ χ' : D'.X) :
    LB.Gen.Corr D'.P.L _ _ _ _
      (LB.mulGen D'.P.L _ _ _ _ (a (χ + χ'))
        (LB.pullGen D'.P.L (thφ D'.P.A (x3 D'.P.A)) thε D'.cub.t
          (lift (toUnit _ ≫ D'.c χ) (lift (toUnit _ ≫ D'.c χ') p')).left))
      (LB.mulGen D'.P.L _ _ _ _ (a χ) (a χ')) := by sorry
