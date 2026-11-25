-- Prove2me | Theorems.Thm_GlobalTheory_TauBalPull_ros_pull
-- name    : GlobalTheory.TauBalPull.ros_pull
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:03:05.746366+00:00
-- url     : https://prove2.me/theorems/396dab93-8468-4ce0-a317-c9e916e654e3
-- title:
--   Tau Bal Pull: ros pull
-- statement:
--   The Tau Bal Pull construction uses the ros pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBalOfIsPullDeg.lean#L118-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBalOfIsPullDeg.lean#L118-L184

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBalOfIsPullDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TauBalPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.TauPull
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem GlobalTheory.TauBalPull.ros_pull (hG : GlobalFnsSt) (hD : IsPullDeg φ D D') {f g : D.P.A ⟶ D.P.A} {f' g' : D'.P.A ⟶ D'.P.A}
    [IsMonHom f] [IsMonHom g]
    (hf : f' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map f)
    (hg : g' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf φ)).map g)
    (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L))
    (u' : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A f' g') rosatiε)) (hu' : u'.IsGen)
    (h₀' : LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u' (zero2 D'.P.A)) (LB.oneGen D'.P.L))
    {T : Over (Sp R')} {z : T.left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (x y : T ⟶ D'.P.A) :
    val u (lift (pushPt (pull_grp hD).1.w x) (pushPt (pull_grp hD).1.w y)).left z J =
      (∏ i, gw hD.w ((lift x y).left ≫ rosatiφ D'.P.A f' g' i) z
        (J (((lift x y).left ≫ rosatiφ D'.P.A f' g' i) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
        (J' ((lift x y).left ≫ rosatiφ D'.P.A f' g' i)) ^ rosatiε i) * val u' (lift x y).left z J' := by sorry
