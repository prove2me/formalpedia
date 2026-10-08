-- Prove2me | Theorems.Thm_KellyReversibility_Genetics_ewens_sampling_consistency_pred
-- name    : KellyReversibility.Genetics.ewens_sampling_consistency_pred
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T03:09:14.673574+00:00
-- url     : https://prove2.me/theorems/acec38d2-76bd-41e1-ae13-e52546eff6ea
-- title:
--   Theorem 7.1, case $m=M-1$ — removing one random individual preserves the Ewens distribution
-- statement:
--   Let $\nu>0$ and $M\ge 2$. Consider a population of $M$ labelled individuals whose allelic types are labelled by natural numbers. Suppose its description is $\mathbf M$ with probability $\pi_M(\mathbf M)$ given by (7.6), and that, given the description $\mathbf M$, the types are some labelling $x_{\mathbf M}$ with that description. A sample of size $M-1$ is chosen uniformly at random without replacement. Then for every description $\mathbf m$ of a set of size $M-1$,
--
--   $$\sum_{\mathbf M}\pi_M(\mathbf M)\,P_{x_{\mathbf M}}(\mathbf m)=\pi_{M-1}(\mathbf m),$$
--
--   where $P_x(\mathbf m)$ is the probability that a uniformly random $(M-1)$-subset of a population with types $x$ has description $\mathbf m$.
--
--   The proof of Theorem 7.1 establishes this case first; the general case follows by removing individuals one at a time.
--
--   **Formalization Note** The statement holds for every choice of the labellings $x_{\mathbf M}$; since $\pi_M>0$, this includes the fact that the sampling probability depends on the population only through its description. Descriptions are partitions; allelic types are natural numbers, so every description is realized by some labelling.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, p. 148, proof of Theorem 7.1 ("This establishes the theorem for the case m = M − 1")

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal
import Definitions.Def_KellyReversibility_Genetics_Ewens
import Definitions.Def_KellyReversibility_Genetics_Sampling

namespace KellyReversibility.Genetics

/-- Kelly (1979), Theorem 7.1, the case `m = M − 1` established first in its proof (p. 148).
A population of `M ≥ 1` labelled individuals has allelic types (labelled by natural numbers);
given that its description is `p`, the types are `x p : Fin M → ℕ` (any labelling with
description `p`). If the description is distributed as the Ewens distribution `π_M`, then a
uniformly random sample of size `M − 1` drawn without replacement has description `q` with
probability `π_{M−1}(q)`. -/
theorem ewens_sampling_consistency_pred (ν : ℝ) (hν : 0 < ν) (M : ℕ) (hM : 2 ≤ M)
    (x : Nat.Partition M → (Fin M → ℕ)) (hx : ∀ p, HasDescription (x p) p)
    (q : Nat.Partition (M - 1)) :
    ∑ p : Nat.Partition M, ewens ν M p * sampleDescProb (x p) (M - 1) q
      = ewens ν (M - 1) q := by sorry

end KellyReversibility.Genetics
