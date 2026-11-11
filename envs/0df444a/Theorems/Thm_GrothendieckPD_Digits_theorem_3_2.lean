-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_theorem_3_2
-- name    : GrothendieckPD.Digits.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:03.440453+00:00
-- url     : https://prove2.me/theorems/a364d18a-6ed5-47f5-a374-6020f0fd291e
-- title:
--   Theorem 3.2: closure and finitary approximability of the graded Gaussian chaos
-- statement:
--   Let $d_i\in\mathbb N$ for $i\in\mathbb N$, and let $\overline{\mathcal H}_d$ be the graded-degree-$d$ chaos of the graded Gaussian space (Eq. 3.4).
--
--   1. **Closure.** Let $p_{n,i}\in\overline{\mathcal H}_{d_i}$ with $\sup_n\|p_{n,i}\|_2<\infty$ for every $i$. Then there exist a subsequence and $p_i\in\overline{\mathcal H}_{d_i}$ such that, along the subsequence, $(p_{n,i})_{i\in\mathbb N}\xrightarrow{d}(p_i)_{i\in\mathbb N}$ with convergence of all mixed (finite) moments $\mathbb E\prod_{i\in S}p_{n,i}^{\kappa_i}$. Consequently, for every $d$, $\{\mathrm{Law}(p):p\in\overline{\mathcal H}_d\}$ is weakly closed.
--   2. **Approximability.** For all $p_i\in\overline{\mathcal H}_{d_i}$ there exist $p_{n,i}\in\mathcal H_{d_i}(X_1,\dots,X_n)$ (degree-$d_i$ chaos of the first $n$ grade-one variables) with $(p_{n,i})_{i\in\mathbb N}\xrightarrow{d}(p_i)_{i\in\mathbb N}$ and convergence of all mixed moments.
--
--   The result, cited by the paper from [HMP24, Jon26], says that the graded space contains, in law, exactly the limits of Gaussian polynomials of fixed degree; it is the compactness input for Lemma 3.3.
--
--   Differences from the source:
--   - encoding: variables X_i^{(d)}, grade d ≥ 1, i = 1, 2, … → coordinates of ℕ+ × ℕ → ℝ under the product of standard Gaussians; X_i^{(d)} is coordinate (d, i), the index i = 0 being an extra unused variable of each grade; reason: countably many i.i.d. N(0,1) variables of each grade, as on pp. 7–8
--   - encoding: p ∈ 𝐇̄_d (closure of a span in L²) → p ∈ L² and p̂_α = 0 whenever gr(α) ≠ d; reason: equivalent because {ψ_α} is an orthonormal basis of L²(X) (p. 7)
--   - encoding: p ∈ H_d(X_1, …, X_n) → p ∈ L² and p̂_α ≠ 0 only for α supported on X_1, …, X_n with |α| = d; reason: the same space via the Hermite expansion
--   - encoding: (p_{n,i})_{i∈ℕ} →d (p_i)_{i∈ℕ} → E φ((p_{n,i})_i) → E φ((p_i)_i) for every bounded continuous φ : ℝ^ℕ → ℝ (product topology); reason: the definition of convergence in distribution of ℝ^ℕ-valued vectors
--   - encoding: sup_n ‖p_{n,i}‖₂ < ∞ → ∃ B, ∀ n, E[p_{n,i}²] ≤ B; reason: same condition
--   - encoding: {Law(p) : p ∈ 𝐇̄_d} weakly closed → the set of probability measures ν on ℝ with ∫ φ dν = E φ(p) for all bounded continuous φ, for some p ∈ 𝐇̄_d, is closed in ProbabilityMeasure ℝ; reason: bounded continuous functions determine a law; ProbabilityMeasure carries the weak topology
--   - generalization: d_i ∈ ℕ, possibly read as positive → d_i ∈ {0, 1, 2, …}; reason: d_i = 0 (constants) is allowed as well; restricting to positive d_i gives the source's statement
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Theorem 3.2 ([HMP24] Herry–Malicet–Poly arXiv:2412.06749; [Jon26] Jones arXiv:2610.16180), p. 8

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_GradedSpace
open MeasureTheory Filter Topology

namespace GrothendieckPD.Digits

/-- Theorem 3.2 ([HMP24, Jon26], p. 8). Let `d_i ∈ ℕ`.
(i) If `p_{n,i} ∈ 𝐇_{d_i}` with `sup_n ‖p_{n,i}‖_2 < ∞` for every `i`, then along a subsequence
`(p_{n,i})_{i ∈ ℕ}` converges in distribution (as an `ℝ^ℕ`-valued random vector) to some
`(p_i)_{i ∈ ℕ}`, `p_i ∈ 𝐇_{d_i}`, with convergence of all mixed finite moments; consequently the
set of laws `{Law(p) : p ∈ 𝐇_d}` is weakly closed for every `d`.
(ii) For all `p_i ∈ 𝐇_{d_i}` there are `p_{n,i} ∈ H_{d_i}(X_1, …, X_n)` with
`(p_{n,i})_{i ∈ ℕ} → (p_i)_{i ∈ ℕ}` in distribution and in all mixed finite moments. -/
theorem theorem_3_2 (d : ℕ → ℕ) :
    (∀ p : ℕ → ℕ → GPoint → ℝ, (∀ n i, InChaos (d i) (p n i)) →
      (∀ i, ∃ B : ℝ, ∀ n, ∫ x, (p n i x) ^ 2 ∂gradedGaussian ≤ B) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ P : ℕ → GPoint → ℝ, (∀ i, InChaos (d i) (P i)) ∧
        (∀ F : BoundedContinuousFunction (ℕ → ℝ) ℝ,
          Tendsto (fun k => ∫ x, F (fun i => p (φ k) i x) ∂gradedGaussian) atTop
            (𝓝 (∫ x, F (fun i => P i x) ∂gradedGaussian))) ∧
        (∀ (S : Finset ℕ) (κ : ℕ → ℕ),
          Tendsto (fun k => ∫ x, ∏ i ∈ S, (p (φ k) i x) ^ (κ i) ∂gradedGaussian) atTop
            (𝓝 (∫ x, ∏ i ∈ S, (P i x) ^ (κ i) ∂gradedGaussian)))) ∧
    (∀ e : ℕ, IsClosed {ν : ProbabilityMeasure ℝ | ∃ p : GPoint → ℝ, InChaos e p ∧
      ∀ F : BoundedContinuousFunction ℝ ℝ,
        ∫ s, F s ∂(ν : Measure ℝ) = ∫ x, F (p x) ∂gradedGaussian}) ∧
    (∀ P : ℕ → GPoint → ℝ, (∀ i, InChaos (d i) (P i)) →
      ∃ p : ℕ → ℕ → GPoint → ℝ, (∀ n i, InFinitaryChaos (d i) n (p n i)) ∧
        (∀ F : BoundedContinuousFunction (ℕ → ℝ) ℝ,
          Tendsto (fun n => ∫ x, F (fun i => p n i x) ∂gradedGaussian) atTop
            (𝓝 (∫ x, F (fun i => P i x) ∂gradedGaussian))) ∧
        (∀ (S : Finset ℕ) (κ : ℕ → ℕ),
          Tendsto (fun n => ∫ x, ∏ i ∈ S, (p n i x) ^ (κ i) ∂gradedGaussian) atTop
            (𝓝 (∫ x, ∏ i ∈ S, (P i x) ^ (κ i) ∂gradedGaussian)))) := by sorry

end GrothendieckPD.Digits
