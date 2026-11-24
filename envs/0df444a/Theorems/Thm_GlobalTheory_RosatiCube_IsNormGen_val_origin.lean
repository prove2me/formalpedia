-- Prove2me | Theorems.Thm_GlobalTheory_RosatiCube_IsNormGen_val_origin
-- name    : GlobalTheory.RosatiCube.IsNormGen.val_origin
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:30:57.86218+00:00
-- url     : https://prove2.me/theorems/6e851469-8d98-41eb-8e3f-fecbdf7607f3
-- title:
--   Is Norm Gen: val origin
-- statement:
--   The Is Norm Gen construction uses the val origin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RosatiCubicalAdditive.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RosatiCubicalAdditive.lean#L21-L26

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

theorem GlobalTheory.RosatiCube.IsNormGen.val_origin {f g : A ⟶ A} {u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)} (hu : IsNormGen L f g u)
    {y : (𝟙_ (Over S)).left} {J} (hJ : Good L y J) : val₂ u y J (1 : 𝟙_ (Over S) ⟶ A) 1 = 1 := by sorry
