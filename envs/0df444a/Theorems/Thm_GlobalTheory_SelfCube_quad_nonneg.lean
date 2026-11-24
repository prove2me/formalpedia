-- Prove2me | Theorems.Thm_GlobalTheory_SelfCube_quad_nonneg
-- name    : GlobalTheory.SelfCube.quad_nonneg
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:17.561798+00:00
-- url     : https://prove2.me/theorems/2270ace4-aa68-4489-9041-f6d07ba3cdac
-- title:
--   Self Cube: quad nonneg
-- statement:
--   The Self Cube construction uses the quad nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AppellHumbertDataOfIsoCube.lean#L33-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AppellHumbertDataOfIsoCube.lean#L33-L76

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

theorem GlobalTheory.SelfCube.quad_nonneg {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (ψ : (Fin g → ℂ) → ℂ) (hψ : Differentiable ℂ ψ) (h0 : ψ 0 ≠ 0)
    (q : (Fin g → ℂ) → ℝ) (hq : Continuous q) (hs : ∀ (t : ℂ) w, q (t • w) = ‖t‖ ^ 2 * q w)
    (hper : ∀ z, ∀ l ∈ Λ, ‖ψ (z + l)‖ * Real.exp (-q (z + l)) = ‖ψ z‖ * Real.exp (-q z)) (w) :
    0 ≤ q w := by sorry
