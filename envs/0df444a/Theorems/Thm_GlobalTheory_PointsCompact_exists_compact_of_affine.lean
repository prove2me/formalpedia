-- Prove2me | Theorems.Thm_GlobalTheory_PointsCompact_exists_compact_of_affine
-- name    : GlobalTheory.PointsCompact.exists_compact_of_affine
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:38.065489+00:00
-- url     : https://prove2.me/theorems/935224e7-0822-493a-b132-30f7b225705d
-- title:
--   Points Compact: exists compact of affine
-- statement:
--   The Points Compact construction uses the exists compact of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CompactSpacePointsPolAV.lean#L67-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CompactSpacePointsPolAV.lean#L67-L120

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

theorem GlobalTheory.PointsCompact.exists_compact_of_affine (h1 : ValueRules) (h2 : AffinePoints) (X : Over (Sp ℂ))
    (U : X.left.Opens) (hU : IsAffineOpen U) {n : ℕ} (r : Fin n → Γ(X.left, U))
    (c : ℂ →+* Γ(X.left, U)) (hc : ∀ a, c a = constFn X.hom U a)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom c r)) :
    ∃ C : Set (𝟙_ (Over (Sp ℂ)) ⟶ X), @IsCompact _ (pointTopology X) C ∧
      ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ X, ⊤ ≤ x.left ⁻¹ᵁ U → (∀ j, ‖valAt' x.left U (r j)‖ ≤ 1) → x ∈ C := by sorry
