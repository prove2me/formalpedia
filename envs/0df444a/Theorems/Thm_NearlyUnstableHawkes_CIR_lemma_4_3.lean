-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_CIR_lemma_4_3
-- name    : NearlyUnstableHawkes.CIR.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:30.183983+00:00
-- url     : https://prove2.me/theorems/a2549824-3b5c-41d2-9d58-f0e5cc974927
-- title:
--   Lemma 4.3 — inverse-frequency decay of the kernel transform
-- statement:
--   Let $\widehat\phi(z)=\int_0^\infty e^{izx}\phi(x)\,dx$, where $\phi$ and its derivative satisfy Assumption 1. There is a finite constant $c>0$ such that
--
--   $$|\widehat\phi(z)|\le\frac{c}{|z|}\qquad(z\ne0).$$
--
--   The estimate provides the high-frequency control needed for the resolvent Fourier bounds.
--
--   **Formalization Note** The source's generic $c$ is existential. The formula is restricted to $z\ne0$, where its denominator is defined.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 16, Lemma 4.3

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_CIR_Setting

open MeasureTheory Filter Topology Set

namespace NearlyUnstableHawkes.CIR

/-- Lemma 4.3, p. 16: inverse-frequency decay of the characteristic function. -/
theorem lemma_4_3 (φ φ' : ℝ → ℝ) (m : ℝ)
    (hφ : Assumption1 φ φ' m) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℝ, z ≠ 0 →
      ‖fourierPlus φ z‖ ≤ c / |z| := by sorry

end NearlyUnstableHawkes.CIR
