-- Prove2me | Theorems.Thm_KellyReversibility_Symmetric_lemma_3_9
-- name    : KellyReversibility.Symmetric.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T02:51:03.364097+00:00
-- url     : https://prove2.me/theorems/c0849e33-16ba-453f-98b0-d86327438ec0
-- title:
--   Lemma 3.9 — mixtures of gamma distributions approximate any positive distribution
-- statement:
--   Let $F$ be the distribution function of a positive random variable $X$, i.e. $\mathbb P(X \le 0) = 0$. Then there is a sequence of distribution functions $F_m$, each the distribution function of a mixture of gamma distributions (countably many components, integer shapes $w \ge 1$, stage means $d > 0$), such that
--   $$\lim_{m \to \infty} F_m(x) = F(x)$$
--   for all $x$ at which $F$ is continuous.
--
--   The lemma is what makes the gamma-mixture results of §3.3 suggest insensitivity for arbitrary service requirement distributions (Theorem 3.10).
--
--   **Formalization Note** $X$ is represented by its law $\mu$, a probability measure on $\mathbb R$ with $\mu((-\infty, 0]) = 0$, and $F$ is Mathlib's `cdf μ`. "Mixture of gamma distributions" is the predicate `IsGammaMixtureCDF` (weights indexed by $\mathbb N$, shape $w$ and rate $1/d$); $F$ itself is in general not such a mixture (e.g. a point mass), so the statement is not trivial.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 77 (PDF p. 80), Lemma 3.9

import Mathlib
import Definitions.Def_KellyReversibility_Symmetric_GammaMixture

namespace KellyReversibility.Symmetric

open MeasureTheory ProbabilityTheory Filter Topology

/-- Kelly 1979, Lemma 3.9 (p. 77): if `F` is the distribution function of a positive random
variable, there are distribution functions `F_m`, each of a mixture of gamma distributions,
with `F_m(x) → F(x)` at every continuity point `x` of `F`. -/
theorem lemma_3_9 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hpos : μ (Set.Iic 0) = 0) :
    ∃ F : ℕ → ℝ → ℝ, (∀ m, IsGammaMixtureCDF (F m)) ∧
      ∀ x, ContinuousAt (cdf μ) x → Tendsto (fun m => F m x) atTop (𝓝 (cdf μ x)) := by sorry

end KellyReversibility.Symmetric
