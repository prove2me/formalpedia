-- Prove2me | Theorems.Thm_GlobalTheory_PointsCompact_compact_of_sections
-- name    : GlobalTheory.PointsCompact.compact_of_sections
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:50:45.537377+00:00
-- url     : https://prove2.me/theorems/d2fa532e-8fea-4fb7-9f69-3278bd145c55
-- title:
--   Points Compact: compact of sections
-- statement:
--   The Points Compact construction uses the compact of sections property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CompactSpacePointsPolAV.lean#L134-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CompactSpacePointsPolAV.lean#L134-L181

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

theorem GlobalTheory.PointsCompact.compact_of_sections (h1 : ValueRules) (h2 : AffinePoints) (X : Over (Sp ℂ))
    (L : LB X.left) {M : ℕ} (s : Fin (M + 1) → LB.Sec L)
    (hcov : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (H : ∀ i, IsAffineOpen (Out.nonzeroLocus (s i)) ∧
      ∃ r : Fin (M + 1) → Γ(X.left, Out.nonzeroLocus (s i)),
        (∀ j k, resG X.left (inf_le_right : Out.nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s j).f k) =
          resG X.left (inf_le_left : Out.nonzeroLocus (s i) ⊓ L.U k ≤ _) (r j) *
          resG X.left (inf_le_right : Out.nonzeroLocus (s i) ⊓ L.U k ≤ L.U k) ((s i).f k)) ∧
        ∃ c : ℂ →+* Γ(X.left, Out.nonzeroLocus (s i)), (∀ a, c a = constFn X.hom _ a) ∧
          Function.Surjective (MvPolynomial.eval₂Hom c r)) :
    @CompactSpace _ (pointTopology X) := by sorry
