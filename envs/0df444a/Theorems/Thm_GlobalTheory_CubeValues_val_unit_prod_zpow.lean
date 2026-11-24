-- Prove2me | Theorems.Thm_GlobalTheory_CubeValues_val_unit_prod_zpow
-- name    : GlobalTheory.CubeValues.val_unit_prod_zpow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:29:42.477095+00:00
-- url     : https://prove2.me/theorems/396101c5-c9f4-4812-a940-934610f7d509
-- title:
--   Cube Values: val unit prod zpow
-- statement:
--   The Cube Values construction uses the val unit prod zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L36-L46

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

theorem GlobalTheory.CubeValues.val_unit_prod_zpow (hv : ValueRules) {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) {K : Type} [Fintype K]
    (f : K → Γ(X, U)ˣ) (ε : K → ℤ) :
    valAt' x U (∏ k, f k ^ ε k).val = ∏ k, valAt' x U (f k).val ^ ε k := by sorry
