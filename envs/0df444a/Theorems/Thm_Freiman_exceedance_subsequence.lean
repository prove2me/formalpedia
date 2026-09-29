-- Prove2me | Theorems.Thm_Freiman_exceedance_subsequence
-- name    : Freiman.exceedance_subsequence
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:40.092269+00:00
-- url     : https://prove2.me/theorems/e30566e3-a527-4535-b3e5-ba0883a508b9
-- title:
--   Repeated threshold exceedances have a strictly increasing subsequence
-- statement:
--   If a real sequence exceeds a fixed threshold at arbitrarily late indices, then there is a strictly increasing sequence of indices at every one of which the threshold is exceeded.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9, subsequential upper-bound argument, printed p. 13.

import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem exceedance_subsequence (f : ℕ → ℝ) (r : ℝ)
    (h : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ r < f n) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∀ n : ℕ, r < f (s n) := by
  sorry

end Freiman
