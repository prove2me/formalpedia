-- Prove2me | Theorems.Thm_GlobalTheory_IntAct_isGen_oneGen
-- name    : GlobalTheory.IntAct.isGen_oneGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:51.525885+00:00
-- url     : https://prove2.me/theorems/4c366873-a90a-40cc-b296-c68667f6a8fa
-- title:
--   Int Act: is Gen one Gen
-- statement:
--   The Int Act construction uses the is Gen one Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RosatiAdjOfPoints.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/RosatiAdjOfPoints.lean#L41-L42

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RosatiAdjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RosatiAdjOfPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.IntAct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem GlobalTheory.IntAct.isGen_oneGen {X Y : Scheme.{0}} (M : LB X) : (LB.oneGen M (Y := Y)).IsGen := by sorry
