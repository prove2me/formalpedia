-- Prove2me | Theorems.Thm_GlobalTheory_torsion_points_distinct_mod_maximal_ideal
-- name    : GlobalTheory.torsion_points_distinct_mod_maximal_ideal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:51:41.956897+00:00
-- url     : https://prove2.me/theorems/c138ecc8-dd4e-4f05-acab-c459932202c3
-- title:
--   Global Theory: torsion points distinct mod maximal ideal
-- statement:
--   The Global Theory construction uses the torsion points distinct mod maximal ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TorsionPointsDistinctModMaximalIdeal.lean#L181-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TorsionPointsDistinctModMaximalIdeal.lean#L181-L201

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TorsionPointsDistinctModMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine
variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem GlobalTheory.torsion_points_distinct_mod_maximal_ideal : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [DecidableEq K] (A B : K) (N : ℕ), ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ‖(2 : K)‖ = 1 → ‖4 * A ^ 3 + 27 * B ^ 2‖ = 1 → Odd N → (∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y), N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x‖ ≤ 1) → ∀ (x y : K) (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y), N • (WeierstrassCurve.Affine.Point.some x y h) = 0 → ‖x ^ 3 + A * x + B‖ = 1 ∧ ∀ (x' y' : K) (h' : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x' y'), N • (WeierstrassCurve.Affine.Point.some x' y' h') = 0 → x ≠ x' → ‖x - x'‖ = 1 := by sorry
