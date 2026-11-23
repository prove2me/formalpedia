-- Prove2me | Theorems.Thm_GlobalTheory_RigidTriv_pull_gen
-- name    : GlobalTheory.RigidTriv.pull_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:23:12.5308+00:00
-- url     : https://prove2.me/theorems/e9bef2e3-931a-448f-a219-ec86859713fa
-- title:
--   Rigid Triv: pull gen
-- statement:
--   The Rigid Triv construction uses the pull gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfRigid.lean#L128-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsGenOfRigid.lean#L128-L144

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RigidTriv
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.RigidTriv.pull_gen {N : LB Y} {F : Z ⟶ Y} {t : (N.pull F).Gen} (ht : t.IsGen) (z : Z) (i j : N.ι)
    (hi : F z ∈ N.U i) (hj : F z ∈ N.U j) :
    gm (𝟙 Z) z ((N.pull F).U (fun _ => i)) (t.s fun _ => i) =
      gm F z (N.U i ⊓ N.U j) (N.g i j) * gm (𝟙 Z) z ((N.pull F).U (fun _ => j)) (t.s fun _ => j) := by sorry
