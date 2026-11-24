-- Prove2me | Theorems.Thm_GlobalTheory_RosatiCube_ros_add_of_surj
-- name    : GlobalTheory.RosatiCube.ros_add_of_surj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:58.027852+00:00
-- url     : https://prove2.me/theorems/a4c320b6-1a6d-4023-b197-42ff8e60d190
-- title:
--   Rosati Cube: ros add of surj
-- statement:
--   The Rosati Cube construction uses the ros add of surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RosatiCubicalAdditive.lean#L46-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RosatiCubicalAdditive.lean#L46-L127

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RosatiCubicalAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RosatiCube
open ReciprocityTheory.ChartRestriction.G.DVR
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
variable {L : LB A.left}
variable {Lr : RigLB A} (c : CubicalStr A Lr)

theorem GlobalTheory.RosatiCube.ros_add_of_surj (sj : Function.Surjective (A ⊗ A ⊗ A).hom.appTop.hom) (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)) (hu : u.IsGen)
    (h₀ : LB.Gen.Corr Lr.L _ _ _ _ (LB.pullGen Lr.L _ _ u (zero2 A)) (LB.oneGen Lr.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x x' y : T ⟶ A) :
    val₂ u z J (x * x') y * cubV c z J x x' (y ≫ g) =
        cubV c z J (x ≫ f) (x' ≫ f) y * (val₂ u z J x y * val₂ u z J x' y) ∧
      val₂ u z J y (x * x') * cubV c z J y (x ≫ g) (x' ≫ g) =
        cubV c z J (y ≫ f) x x' * (val₂ u z J y x * val₂ u z J y x') := by sorry
