-- Prove2me | Theorems.Thm_GlobalTheory_CubeValues_val_cocycle
-- name    : GlobalTheory.CubeValues.val_cocycle
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:29:24.327051+00:00
-- url     : https://prove2.me/theorems/7bf50a8f-6120-4e9a-a172-511cafd7ebe8
-- title:
--   Cube Values: val cocycle
-- statement:
--   The Cube Values construction uses the val cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L91-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L91-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
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
open GlobalTheory GlobalTheory.CubeValues
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

theorem GlobalTheory.CubeValues.val_cocycle (hv : ValueRules) {L : LB X} (hL : L.IsLB) (i j k : L.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j) (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valAt' x (L.U i ⊓ L.U j) (L.g i j).val * valAt' x (L.U j ⊓ L.U k) (L.g j k).val =
      valAt' x (L.U i ⊓ L.U k) (L.g i k).val := by sorry
