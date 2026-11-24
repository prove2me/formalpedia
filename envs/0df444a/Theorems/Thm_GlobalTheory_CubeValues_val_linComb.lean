-- Prove2me | Theorems.Thm_GlobalTheory_CubeValues_val_linComb
-- name    : GlobalTheory.CubeValues.val_linComb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:03:08.901146+00:00
-- url     : https://prove2.me/theorems/26b3922a-c3b8-4f26-9cf8-21d2673ec2bd
-- title:
--   Cube Values: val lin Comb
-- statement:
--   The Cube Values construction uses the val lin Comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L78-L89

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

theorem GlobalTheory.CubeValues.val_linComb (hv : ValueRules) {Y : Scheme.{0}} (L : LB Y) {K : Type} [Fintype K]
    (φ : K → (X ⟶ Y)) (ε : K → ℤ) (j j' : K → L.ι)
    (hj : ⊤ ≤ x ⁻¹ᵁ L.wchart φ j) (hj' : ⊤ ≤ x ⁻¹ᵁ L.wchart φ j') :
    valAt' x (L.wchart φ j ⊓ L.wchart φ j') ((L.LinComb φ ε).g j j').val =
      ∏ k, valAt' (x ≫ φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)).val ^ ε k := by sorry
