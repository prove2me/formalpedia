-- Prove2me | Theorems.Thm_KellyReversibility_Genetics_quasi_fixation_probability
-- name    : KellyReversibility.Genetics.quasi_fixation_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:08:59.327499+00:00
-- url     : https://prove2.me/theorems/4ef96e33-134f-4858-930a-2e8a666f7257
-- title:
--   Theorem 7.9 — probability of quasi-fixation of a new allele, $Q^{-1}=\sum_{i=0}^{M-1}\binom{M-1}{i}^{-1}\binom{\nu+M-1}{i}$
-- statement:
--   Let $M\ge 2$ be the population size, $\mu>0$ the death rate and $0<u<1$ the mutation probability, and put $\nu=(M-1)u/(1-u)$ as in (7.5). Let $Q$ be the probability that the allele-frequency random walk with intensities (7.8), started at $1$ (a new allele, represented by one individual), reaches $M$ (quasi-fixation: the allele is the only one present) before it reaches $0$. Then
--
--   $$Q^{-1}=\sum_{i=0}^{M-1}\binom{M-1}{i}^{-1}\binom{\nu+M-1}{i},$$
--
--   where $\binom{\nu+M-1}{i}=(\nu+M-1)(\nu+M-2)\cdots(\nu+M-i)/i!$ is the generalized binomial coefficient.
--
--   For example, for $M=2$ this gives $Q=(1-u)/(2-u)$. The result is used to compute the mean time between quasi-fixations (Corollary 7.10).
--
--   **Formalization Note** $Q$ is `quasiFixProb μ u M`, the limit of the probabilities that the jump chain of the walk reaches $M$ within $n$ jumps without reaching $0$. Since $Q>0$, the equation determines $Q$; a junk value $Q=0$ would make the left side $0$, which the positive right side excludes.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 157, Theorem 7.9 (walk (7.8), p. 153; ν from (7.5), p. 146)

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal
import Definitions.Def_KellyReversibility_Genetics_QuasiFixation

namespace KellyReversibility.Genetics

open AppliedComb.GenFun

/-- Kelly (1979), Theorem 7.9, p. 157. The probability that a new allele will become
quasi-fixed is `Q`, where `Q⁻¹ = ∑_{i=0}^{M−1} C(M − 1, i)⁻¹ C(ν + M − 1, i)`.
Here `M ≥ 2` is the population size, `μ > 0` the death rate, `0 < u < 1` the mutation
probability, `ν = (M − 1) u / (1 − u)` (7.5), and `Q` is the probability that the walk (7.8)
started at `1` reaches `M` before `0`. -/
theorem quasi_fixation_probability (μ u ν : ℝ) (M : ℕ) (hμ : 0 < μ) (hu0 : 0 < u)
    (hu1 : u < 1) (hM : 2 ≤ M) (hν : ν = ((M : ℝ) - 1) * u / (1 - u)) :
    (quasiFixProb μ u M)⁻¹
      = ∑ i ∈ Finset.range M, ((Nat.choose (M - 1) i : ℝ))⁻¹ * binomReal (ν + (M : ℝ) - 1) i := by sorry

end KellyReversibility.Genetics
