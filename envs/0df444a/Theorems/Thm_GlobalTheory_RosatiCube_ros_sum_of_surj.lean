-- Prove2me | Theorems.Thm_GlobalTheory_RosatiCube_ros_sum_of_surj
-- name    : GlobalTheory.RosatiCube.ros_sum_of_surj
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:47.154888+00:00
-- url     : https://prove2.me/theorems/5c9b8dab-c839-454a-9712-2a4b4002de13
-- title:
--   Rosati Cube: ros sum of surj
-- statement:
--   The Rosati Cube construction uses the ros sum of surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RosatiCubicalAdditive.lean#L129-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RosatiCubicalAdditive.lean#L129-L165

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

theorem GlobalTheory.RosatiCube.ros_sum_of_surj (sj : Function.Surjective (A ⊗ A).hom.appTop.hom) {f g f₁ g₁ f₂ g₂ : A ⟶ A}
    (hf : f = f₁ * f₂) (hg : g = g₁ * g₂) {u : LB.Gen (LB.LinComb Lr.L (rosatiφ A f g) rosatiε)}
    {u₁ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₁ g₁) rosatiε)} {u₂ : LB.Gen (LB.LinComb Lr.L (rosatiφ A f₂ g₂) rosatiε)}
    (hu : IsNormGen Lr.L f g u) (hu₁ : IsNormGen Lr.L f₁ g₁ u₁) (hu₂ : IsNormGen Lr.L f₂ g₂ u₂) {T : Over S} {z : T.left} {J}
    (hJ : Good Lr.L z J) (x w : T ⟶ A) :
    val₂ u z J x w * cubV c z J x (w ≫ g₁) (w ≫ g₂) =
      cubV c z J (x ≫ f₁) (x ≫ f₂) w * (val₂ u₁ z J x w * val₂ u₂ z J x w) := by sorry
