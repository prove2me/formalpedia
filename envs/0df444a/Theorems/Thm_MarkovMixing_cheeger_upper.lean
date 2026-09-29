-- Prove2me | Theorems.Thm_MarkovMixing_cheeger_upper
-- name    : MarkovMixing.cheeger_upper
-- status  : Proved
-- author  : @chenmin
-- created : 2026-08-22T16:45:41.330487+00:00
-- url     : https://prove2.me/theorems/8e914dfd-cd15-4c4b-b173-c4c80670bd47
-- title:
--   Theorem 13.14, upper bound: $\gamma \le 2\Phi_\star$
-- statement:
--   Let $P$ be an irreducible transition matrix on a finite state space $V$ with $|V| \ge 2$, reversible with respect to its stationary distribution $\pi$. Two quantities measure how slowly the chain moves.
--
--   The **spectral gap** is $\gamma = 1 - \lambda_2$, where $\lambda_2$ is the largest eigenvalue of $P$ other than $1$ — an analytic quantity.
--
--   The **bottleneck ratio** is a geometric quantity: writing $Q(x,y) = \pi(x)P(x,y)$ for the edge measure and
--   $$\Phi(S) = \frac{\sum_{x \in S}\sum_{y \notin S} Q(x,y)}{\pi(S)}$$
--   for the probability flow out of $S$ per unit of stationary mass, one sets
--   $$\Phi_\star = \min\{\Phi(S) : S \ne \emptyset,\ \pi(S) \le \tfrac12\}.$$
--
--   **Claim.** $\gamma \le 2\,\Phi_\star$.
--
--   This is the easy half of the discrete Cheeger inequality (Theorem 13.14 of Levin--Peres--Wilmer), and it is the direction with the clean interpretation: a chain with a bottleneck cannot have a large spectral gap, hence cannot mix quickly. The proof is a single test function: for a set $S$ with $\pi(S) \le \tfrac12$ take
--   $$f_S(x) = \begin{cases} -\pi(S^c), & x \in S,\\ \pi(S), & x \notin S,\end{cases}$$
--   which has $\mathbb E_\pi(f_S) = 0$, variance $\pi(S)\pi(S^c)$ and Dirichlet energy $Q(S,S^c)$; the variational characterization of $\gamma$ then gives $\gamma \le Q(S,S^c)/[\pi(S)\pi(S^c)] \le 2\Phi(S)$, using $\pi(S^c) \ge \tfrac12$.
--
--   The reverse inequality $\Phi_\star^2/2 \le \gamma$ is the substantial half.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 13.3.2, Theorem 13.14, 'Proof of upper bound in Theorem 13.14', pp. 177-178

import Definitions.Def_mm_spectral
import Definitions.Def_mm_lower

namespace MarkovMixing

/-- **Theorem 13.14, upper bound** (Jerrum--Sinclair, Lawler--Sokal; LPW): the
spectral gap of a reversible irreducible chain is at most twice its bottleneck
ratio, `γ ≤ 2Φ⋆`. -/
theorem cheeger_upper {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (hV : 2 ≤ Fintype.card V) (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π) :
    spectralGap P ≤ 2 * bottleneckStar P π := by
  sorry

end MarkovMixing
