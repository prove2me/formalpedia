-- Prove2me | Theorems.Thm_GlobalTheory_CubeValues_val_pullU
-- name    : GlobalTheory.CubeValues.val_pullU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:57.433082+00:00
-- url     : https://prove2.me/theorems/9d93a1ae-b16e-49c6-8fb7-9c3a33a37b81
-- title:
--   Cube Values: val pull U
-- statement:
--   The Cube Values construction uses the val pull U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L52-L54

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

theorem GlobalTheory.CubeValues.val_pullU (hv : ValueRules) {Y : Scheme.{0}} (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)ˣ) :
    valAt' x (φ ⁻¹ᵁ U) (pullU φ U f).val = valAt' (x ≫ φ) U f.val := by sorry
