-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGroupFrame_top_le_wchart_two
-- name    : GlobalTheory.ThetaGroupFrame.top_le_wchart_two
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:02:17.67927+00:00
-- url     : https://prove2.me/theorems/c418624f-46e3-40e5-b9a3-072dfa365df8
-- title:
--   Theta Group Frame: top le wchart two
-- statement:
--   The Theta Group Frame construction uses the top le wchart two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsConstOfCover.lean#L92-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsConstOfCover
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
open GlobalTheory GlobalTheory.ThetaGroupFrame

theorem GlobalTheory.ThetaGroupFrame.top_le_wchart_two {X Y Z : Scheme.{0}} (L : LB X) (φ₀ φ₁ : Y ⟶ X) (j : Fin 2 → L.ι)
    (x : Z ⟶ Y) (y₀ y₁ : Z ⟶ X) (h₀ : x ≫ φ₀ = y₀) (h₁ : x ≫ φ₁ = y₁) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L ![φ₀, φ₁] j ↔ ⊤ ≤ y₀ ⁻¹ᵁ L.U (j 0) ∧ ⊤ ≤ y₁ ⁻¹ᵁ L.U (j 1) := by sorry
