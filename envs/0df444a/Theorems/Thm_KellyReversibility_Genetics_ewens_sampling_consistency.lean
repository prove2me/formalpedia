-- Prove2me | Theorems.Thm_KellyReversibility_Genetics_ewens_sampling_consistency
-- name    : KellyReversibility.Genetics.ewens_sampling_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:09:20.545672+00:00
-- url     : https://prove2.me/theorems/8fb826f7-56e3-48b7-9749-5efff8a0e456
-- title:
--   Theorem 7.1 — the Ewens distribution is consistent under sampling without replacement
-- statement:
--   Let $\nu>0$, $M\ge2$ and $1\le m\le M$. Consider a population of $M$ labelled individuals, with allelic types labelled by natural numbers. Suppose the population has the description $\mathbf M$ with probability $\pi_M(\mathbf M)$ given by the Ewens distribution (7.6), and that, given its description $\mathbf M$, the individuals' types are some labelling $x_{\mathbf M}$ with that description. A random sample of size $m$ is chosen without replacement, i.e. a uniformly random $m$-element subset of the population. Then the sample has the description $\mathbf m$ with probability $\pi_m(\mathbf m)$:
--
--   $$\sum_{\mathbf M:\ \sum_i iM_i=M}\pi_M(\mathbf M)\,P_{x_{\mathbf M}}(\mathbf m)=\pi_m(\mathbf m)\qquad\text{for every description }\mathbf m\text{ with }\sum_i i m_i=m,$$
--
--   where $P_x(\mathbf m)$ is $\binom{M}{m}^{-1}$ times the number of $m$-subsets of the population whose members' types have description $\mathbf m$. The same value of $\nu$ is used for both population sizes.
--
--   The theorem says that the sampling distribution of a sample of size $m$ from a population of size $M$ is the equilibrium distribution given by the Ewens formula for a population of size $m$.
--
--   **Formalization Note** Descriptions are partitions of the population size (`Nat.Partition`), with $M_i$ the multiplicity of the part $i$. The sampling probability is defined by counting subsets of labelled individuals. The statement holds for every choice of labellings $x_{\mathbf M}$; since $\pi_M>0$, this includes the fact that the sampling probability depends on the population only through its description. Allelic types are natural numbers, so every description is realized by some labelling and the hypothesis on $x$ is satisfiable.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 147, Theorem 7.1

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal
import Definitions.Def_KellyReversibility_Genetics_Ewens
import Definitions.Def_KellyReversibility_Genetics_Sampling

namespace KellyReversibility.Genetics

/-- Kelly (1979), Theorem 7.1, p. 147. Suppose that a random sample of size `m` is chosen
without replacement from a population of size `M`, `m ≤ M`. If the population has the
description `M` with probability `π_M(M)` then the sample has the description `m` with
probability `π_m(m)` (the Ewens distribution (7.6), with the same `ν > 0` for both sizes).

The population is `Fin M`, with allelic types labelled by natural numbers; given description
`p` its types are `x p`, an arbitrary labelling with description `p`. The sample is a
uniformly random `m`-subset of `Fin M`. -/
theorem ewens_sampling_consistency (ν : ℝ) (hν : 0 < ν) (M m : ℕ)
    (hM : 2 ≤ M) (hm : 1 ≤ m) (hmM : m ≤ M)
    (x : Nat.Partition M → (Fin M → ℕ)) (hx : ∀ p, HasDescription (x p) p)
    (q : Nat.Partition m) :
    ∑ p : Nat.Partition M, ewens ν M p * sampleDescProb (x p) m q = ewens ν m q := by sorry

end KellyReversibility.Genetics
