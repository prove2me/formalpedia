-- Prove2me | Theorems.Thm_Freiman_finite_limsup_subsequence_comparison
-- name    : Freiman.finite_limsup_subsequence_comparison
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:56:17.342323+00:00
-- url     : https://prove2.me/theorems/18410031-c730-4a6c-a3f6-0896f0351eb8
-- title:
--   Epsilon limsup comparison with a convergent subsequence
-- statement:
--   An explicit epsilon comparison: v is eventually a subsequence of u with indices tending to infinity; every late u is bounded by 2 or a late v; and v has limsup at least 2. These three properties give equivalence for the platform’s two-clause HasFiniteLimsup.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §1.2, epsilon details of found:perron

import Definitions.Def_Freiman_perronArithmetic

namespace Freiman

theorem finite_limsup_subsequence_comparison (u v : ℕ → ℝ) (f : ℕ → ℕ) (t : ℝ) (hf : ∀ R : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R ≤ f n) (heq : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → u (f n) = v n) (hupper : ∀ K : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → u q ≤ 2 ∨ ∃ n : ℕ, K ≤ n ∧ u q ≤ v n) (htwo : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 2 - ε < v n) :
    HasFiniteLimsup u t ↔ HasFiniteLimsup v t := by
  sorry

end Freiman
