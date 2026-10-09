-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_CIR_lemma_4_2
-- name    : NearlyUnstableHawkes.CIR.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:06.913196+00:00
-- url     : https://prove2.me/theorems/68a6360a-a041-4dbe-a696-ee0288860cb8
-- title:
--   Lemma 4.2 — the kernel characteristic function stays away from one
-- statement:
--   Let $\widehat\phi(z)=\int_0^\infty e^{izx}\phi(x)\,dx$ be the characteristic function of the nonnegative density $\phi$ from Assumption 1. For every $\delta>0$ there is $\varepsilon>0$ such that
--
--   $$|1-\widehat\phi(z)|\ge\varepsilon\qquad\text{whenever }|z|\ge\delta.$$
--
--   This excludes additional frequencies at which the renewal denominator vanishes.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 16, Lemma 4.2

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_CIR_Setting

open MeasureTheory Filter Topology Set

namespace NearlyUnstableHawkes.CIR

/-- Lemma 4.2, p. 16: the characteristic function stays away from one off zero. -/
theorem lemma_4_2 (φ φ' : ℝ → ℝ) (m : ℝ)
    (hφ : Assumption1 φ φ' m) :
    ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧
      ∀ z : ℝ, δ ≤ |z| → ε ≤ ‖(1 : ℂ) - fourierPlus φ z‖ := by sorry

end NearlyUnstableHawkes.CIR
