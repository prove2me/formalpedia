-- Prove2me | Theorems.Thm_ModernOnlineLearning_LowerBounds_probabilistic_method
-- name    : ModernOnlineLearning.LowerBounds.probabilistic_method
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:26.112743+00:00
-- url     : https://prove2.me/theorems/ac799882-243b-4908-8f0b-6bf8d0fca3ca
-- title:
--   §5.1, p. 50 — a random sequence attaining at least its expected loss
-- statement:
--   Let $\Omega$ be a finite set of possible random sequences with probabilities $p(\omega)\ge0$ summing to one. If a real loss $F(\omega)$ has expectation at least $K$, then some sequence with positive probability has loss at least $K$:
--
--   $$
--   K\le\sum_{\omega\in\Omega}p(\omega)F(\omega)
--   \quad\Longrightarrow\quad
--   \exists\,\omega\in\Omega:\ p(\omega)>0\ \text{and}\ F(\omega)\ge K.
--   $$
--
--   This is the finite probabilistic-method step used to turn an expected regret lower bound into a deterministic hard loss sequence.
--
--   **Formalization Note** The source describes general random sequences. The finite version covers the Rademacher construction used immediately afterward and has an ordinary finite expectation.
-- source:
--   Orabona, arXiv:1912.13213v10, §5.1, p. 50, display and following paragraph before Theorem 5.1

import Mathlib

namespace ModernOnlineLearning.LowerBounds

/-- The first-moment existence step from §5.1, printed p. 50. For a finite
random sequence, if its mean loss is at least `K`, some sequence in the
support has loss at least `K`. -/
theorem probabilistic_method {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (F : Ω → ℝ) (K : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hsum : ∑ ω, p ω = 1)
    (hmean : K ≤ ∑ ω, p ω * F ω) :
    ∃ ω, 0 < p ω ∧ K ≤ F ω := by sorry

end ModernOnlineLearning.LowerBounds
