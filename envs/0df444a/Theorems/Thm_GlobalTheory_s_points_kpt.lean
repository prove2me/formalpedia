-- Prove2me | Theorems.Thm_GlobalTheory_s_points_kpt
-- name    : GlobalTheory.s_points_kpt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:21:26.063469+00:00
-- url     : https://prove2.me/theorems/ddef95a4-ae00-41d4-a76e-8504dd2f0c18
-- title:
--   Global Theory: s points kpt
-- statement:
--   The Global Theory construction uses the s points kpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowDvdOfVanishingAtPerfectValuationPoints.lean#L25-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PowDvdOfVanishingAtPerfectValuationPoints.lean#L25-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BoundedPowersOrExistsValuationSubringDvdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionValuationRingCompleteValuationDomaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdicCompletionPrincipalPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory

theorem GlobalTheory.s_points_kpt : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u x : R), ((l : ℕ) : R) = 0 →
    u ∈ nonZeroDivisors R → (∀ r, IsUnit (1 - u * r)) →
    (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → f x = 0) →
    ∀ M : ℕ, ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * x ^ n := by sorry
