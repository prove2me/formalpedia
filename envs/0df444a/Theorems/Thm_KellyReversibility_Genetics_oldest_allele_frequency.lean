-- Prove2me | Theorems.Thm_KellyReversibility_Genetics_oldest_allele_frequency
-- name    : KellyReversibility.Genetics.oldest_allele_frequency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:09:03.239687+00:00
-- url     : https://prove2.me/theorems/aaa27ddd-52dd-4f5b-a94e-915c725e7aa8
-- title:
--   Corollary 7.5 (proof identity) — allele frequency of a random individual under the Ewens distribution
-- statement:
--   Let $\nu>0$, $M\ge 2$ and $1\le i\le M$. Consider a population of $M$ labelled individuals with allelic types labelled by natural numbers, whose description $\mathbf M$ is distributed according to the Ewens distribution $\pi_M$ of (7.6); given $\mathbf M$, the types are some labelling $x_{\mathbf M}$ with that description. Then the probability that the allelic type of an individual chosen uniformly from the population is represented by exactly $i$ individuals is
--
--   $$\sum_{\mathbf M}F_{x_{\mathbf M}}(i)\,\pi_M(\mathbf M)=\frac{\nu}{M}\binom{\nu+M-1}{i}^{-1}\binom{M}{i}, \qquad (7.9)$$
--
--   where $F_x(i)$ is the proportion of individuals whose type is carried by exactly $i$ individuals, and $\binom{\nu+M-1}{i}$ is the generalized binomial coefficient.
--
--   In the book, Corollary 7.5 states that (7.9) is the equilibrium probability that the *oldest* allele is represented by $i$ individuals. Its proof reduces this, via the reversibility of Theorem 7.2, to the frequency of the allele of a randomly chosen individual, and evaluates that with (7.6). The identity above is that evaluation.
--
--   **Formalization Note** Only the combinatorial identity of the proof is formalized. The identification of the frequency of the oldest allele with that of a randomly chosen individual (allele ages, Theorem 7.2 and reversibility) is not formalized. The identity holds for every choice of labellings $x_{\mathbf M}$.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 154, Corollary 7.5, Eq. (7.9) and its proof

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal
import Definitions.Def_KellyReversibility_Genetics_Ewens
import Definitions.Def_KellyReversibility_Genetics_Sampling

namespace KellyReversibility.Genetics

open AppliedComb.GenFun

/-- Kelly (1979), Corollary 7.5, p. 154, the identity of its proof. In equilibrium (population
description distributed as the Ewens distribution `π_M`, `ν > 0`), the probability that the
allelic type of a uniformly chosen individual is represented by exactly `i` individuals of the
population is, for `i = 1, 2, …, M`,
`(ν/M) C(ν + M − 1, i)⁻¹ C(M, i)`  (7.9).
Given description `p`, the types are `x p`, an arbitrary labelling with description `p`. -/
theorem oldest_allele_frequency (ν : ℝ) (hν : 0 < ν) (M i : ℕ) (hM : 2 ≤ M)
    (hi : 1 ≤ i) (hiM : i ≤ M)
    (x : Nat.Partition M → (Fin M → ℕ)) (hx : ∀ p, HasDescription (x p) p) :
    ∑ p : Nat.Partition M, individualFreqProb (x p) i * ewens ν M p
      = ν / (M : ℝ) * (binomReal (ν + (M : ℝ) - 1) i)⁻¹ * (M.choose i : ℝ) := by sorry

end KellyReversibility.Genetics
