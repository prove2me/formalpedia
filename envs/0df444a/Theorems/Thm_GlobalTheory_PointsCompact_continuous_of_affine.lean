-- Prove2me | Theorems.Thm_GlobalTheory_PointsCompact_continuous_of_affine
-- name    : GlobalTheory.PointsCompact.continuous_of_affine
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:43.041117+00:00
-- url     : https://prove2.me/theorems/9dfd6990-0468-4df8-af61-37125bc29ef5
-- title:
--   Points Compact: continuous of affine
-- statement:
--   The Points Compact construction uses the continuous of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CompactSpacePointsPolAV.lean#L22-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CompactSpacePointsPolAV.lean#L22-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CompactSpacePointsPolAV
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
open GlobalTheory GlobalTheory.PointsCompact

theorem GlobalTheory.PointsCompact.continuous_of_affine (h1 : ValueRules) (X : Over (Sp ℂ)) (U : X.left.Opens)
    (hU : IsAffineOpen U) {Z : Type} [TopologicalSpace Z] (σ : Z → (𝟙_ (Over (Sp ℂ)) ⟶ X))
    (hσ : ∀ w, ⊤ ≤ (σ w).left ⁻¹ᵁ U)
    (hc : ∀ f : Γ(X.left, U), Continuous fun w => valAt' (σ w).left U f) :
    @Continuous _ _ _ (pointTopology X) σ := by sorry
