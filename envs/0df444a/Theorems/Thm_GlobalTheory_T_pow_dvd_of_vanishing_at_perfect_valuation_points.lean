-- Prove2me | Theorems.Thm_GlobalTheory_T_pow_dvd_of_vanishing_at_perfect_valuation_points
-- name    : GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:55:36.506261+00:00
-- url     : https://prove2.me/theorems/d4bc31d5-75c4-489e-89fa-6bc088fb824f
-- title:
--   T: pow dvd of vanishing at perfect valuation points
-- statement:
--   The T construction uses the pow dvd of vanishing at perfect valuation points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowDvdOfVanishingAtPerfectValuationPointsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowDvdOfVanishingAtPerfectValuationPointsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPointsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u x : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → f x = 0) → ∀ M : ℕ, ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n := by sorry
