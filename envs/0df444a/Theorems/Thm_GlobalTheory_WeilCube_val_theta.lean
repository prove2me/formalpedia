-- Prove2me | Theorems.Thm_GlobalTheory_WeilCube_val_theta
-- name    : GlobalTheory.WeilCube.val_theta
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:53:46.326199+00:00
-- url     : https://prove2.me/theorems/ba0356e9-8f92-4a0c-b5c7-8795ed44507a
-- title:
--   Weil Cube: val theta
-- statement:
--   The Weil Cube construction uses the val theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean#L90-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/WeilIsGrpPullbackIff.lean#L90-L123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_ThetaMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_WeilIsGrpPullbackIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
open GlobalTheory.WeilCube
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {Lr : RigLB A} (c : CubicalStr A Lr)

theorem GlobalTheory.WeilCube.val_theta (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {k : ℕ} {T : Over S} (θ : ThetaGrp A Lr.L k T)
    (hx : θ.pt ^ k = 1) {T' : Over S} (σ : T' ⟶ T ⊗ A) (z : T'.left) (J) (hJ : Good Lr.L z J) :
    val θ.φ σ.left z J = cubN (cubV c z J) k 1 (σ ≫ fst T A ≫ θ.pt) (σ ≫ snd T A) *
      val θ.φ (lift (σ ≫ fst T A) (1 : T' ⟶ A)).left z J := by sorry
