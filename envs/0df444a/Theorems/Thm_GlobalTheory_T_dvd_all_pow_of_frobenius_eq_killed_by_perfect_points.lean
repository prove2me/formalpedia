-- Prove2me | Theorems.Thm_GlobalTheory_T_dvd_all_pow_of_frobenius_eq_killed_by_perfect_points
-- name    : GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:31.375122+00:00
-- url     : https://prove2.me/theorems/9aa4d34c-91fd-4a21-8d35-aa076a8b8389
-- title:
--   T: dvd all pow of frobenius eq killed by perfect points
-- statement:
--   The T construction uses the dvd all pow of frobenius eq killed by perfect points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdAllPowOfFrobeniusEqKilledByPerfectPointsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/DvdAllPowOfFrobeniusEqKilledByPerfectPointsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdAllPowOfFrobeniusEqKilledByPerfectPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdAllPowOfFrobeniusEqKilledByPerfectPointsStatement
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

theorem GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → ∀ j, f (D j) = 0) → ∀ (m : ℕ) j, u ^ m ∣ D j := by sorry
