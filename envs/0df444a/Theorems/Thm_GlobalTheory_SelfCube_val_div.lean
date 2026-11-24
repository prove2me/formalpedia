-- Prove2me | Theorems.Thm_GlobalTheory_SelfCube_val_div
-- name    : GlobalTheory.SelfCube.val_div
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:16.899535+00:00
-- url     : https://prove2.me/theorems/3e96c680-f4d2-4df6-a620-8cea84a3fcf1
-- title:
--   Self Cube: val div
-- statement:
--   The Self Cube construction uses the val div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AppellHumbertDataOfIsoCube.lean#L226-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AppellHumbertDataOfIsoCube.lean#L226-L244

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.SelfCube
open GlobalTheory.CubeValues

theorem GlobalTheory.SelfCube.val_div (hv : ValueRules) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (M L : LB X)
    (p q : M.ι × L.ι) (hp : ⊤ ≤ x ⁻¹ᵁ (M.U p.1 ⊓ L.U p.2)) (hq : ⊤ ≤ x ⁻¹ᵁ (M.U q.1 ⊓ L.U q.2)) :
    valAt' x ((LB.div M L).U p ⊓ (LB.div M L).U q) ((LB.div M L).g p q).val *
      valAt' x (L.U p.2 ⊓ L.U q.2) (L.g p.2 q.2).val =
      valAt' x (M.U p.1 ⊓ M.U q.1) (M.g p.1 q.1).val := by sorry
