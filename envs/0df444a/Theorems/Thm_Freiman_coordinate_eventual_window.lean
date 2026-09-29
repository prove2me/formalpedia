-- Prove2me | Theorems.Thm_Freiman_coordinate_eventual_window
-- name    : Freiman.coordinate_eventual_window
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:55:44.78998+00:00
-- url     : https://prove2.me/theorems/559f5922-b1e0-4774-8a59-a0ffe9799d82
-- title:
--   Coordinatewise eventual agreement gives eventual agreement on a finite window
-- statement:
--   If each coordinate of a sequence of two-sided words eventually agrees with a fixed word, then the sequence eventually agrees with that word simultaneously on any specified finite integer window.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.1, cylinder continuity and local values, printed p. 7; finite-window step in §1.2, Theorem 1.3, printed p. 8.

import Definitions.Def_Freiman_symbolicMarkovSpectrum
import Mathlib.Topology.Instances.Real.Lemmas

namespace Freiman

theorem coordinate_eventual_window (A : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+)
    (h : ∀ i : ℤ, ∀ᶠ n in Filter.atTop, A n i = b i) (i : ℤ) (R : ℕ) :
    ∀ᶠ n in Filter.atTop, ∀ j : ℤ,
      i - (R : ℤ) ≤ j → j ≤ i + (R : ℤ) → A n j = b j := by
  sorry

end Freiman
