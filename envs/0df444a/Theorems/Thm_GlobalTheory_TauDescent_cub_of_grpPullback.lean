-- Prove2me | Theorems.Thm_GlobalTheory_TauDescent_cub_of_grpPullback
-- name    : GlobalTheory.TauDescent.cub_of_grpPullback
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:25:38.931208+00:00
-- url     : https://prove2.me/theorems/b2201a13-72fc-504d-89c4-d7f476c67170
-- title:
--   Tau Descent: cub of grp Pullback
-- statement:
--   The Tau Descent construction uses the cub of grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TauBimultOfBaseChange.lean#L30-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TauBimultOfBaseChange.lean#L30-L71

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TauBimultOfBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
noncomputable section
open GlobalTheory
open GlobalTheory.TauDescent
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} {β : D'.P.A.left ⟶ D.P.A.left}

theorem GlobalTheory.TauDescent.cub_of_grpPullback (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β)
    (v : LB.Iso D'.P.L (D.P.L.pull β)) (hvg : v.IsGen) {T' : Over (Sp R')} {z : T'.left} {J J'}
    (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (x x' y : T' ⟶ D'.P.A) :
    val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t
        ((lift x (lift x' y)).left ≫ (cubeMapOf gp).F3) z J =
      (∏ I : thK.{0}, gw v ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) z
        (J (((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I) ≫ β))
        (J' ((lift x (lift x' y)).left ≫ thφ D'.P.A (x3 D'.P.A) I)) ^ thε I) * cubV D'.cub z J' x x' y := by sorry
