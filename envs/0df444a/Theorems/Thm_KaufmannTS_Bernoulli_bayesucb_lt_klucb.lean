-- Prove2me | Theorems.Thm_KaufmannTS_Bernoulli_bayesucb_lt_klucb
-- name    : KaufmannTS.Bernoulli.bayesucb_lt_klucb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:24:53.711504+00:00
-- url     : https://prove2.me/theorems/ba93def9-aea6-47a9-80c7-6f3468502d93
-- title:
--   §2, p. 3 — the Bayes-UCB index is below the KL-UCB index, $q_{a,t} < u_{a,t}$
-- statement:
--   Fix a horizon $T\ge 3$, a round $t$ with $1\le t\le T$, and an arm that has produced $S$ successes in $N\ge S$ draws. Let $u$ be its KL-UCB index,
--   $$u=\sup\Big\{x\in[S/N,1):N\,K(S/N,x)\le\ln t+\ln\ln T\Big\},$$
--   and let $q$ be its Bayes-UCB index, the quantile of order $1-\frac{1}{t\ln T}$ of the posterior $\mathrm{Beta}(S+1,N-S+1)$. Then
--   $$q<u.$$
--
--   This comparison lets the analysis of Thompson Sampling replace the sample of a suboptimal arm, which rarely exceeds the Bayes-UCB quantile, by the KL-UCB index, for which counting arguments are available.
--
--   **Formalization Note** The paper cites this fact from Kaufmann, Cappé and Garivier (reference [9]) and does not prove it. The range $1\le t\le T$, $T\ge3$ is the one in which the paper uses the indices; it makes $\ln t+\ln\ln T\ge0$ and $1/(t\ln T)<1$. For $N=0$ or $S=N$ the KL-UCB index is $1$ by the convention of the Model definition.
-- source:
--   Kaufmann, Korda, Munos, Thompson Sampling: An Asymptotically Optimal Finite Time Analysis, arXiv:1205.4217v2, p. 3, §2 (last bullet), cited from [9]

import Mathlib
import Definitions.Def_KaufmannTS_Bernoulli_Model
open MeasureTheory ProbabilityTheory BanditAlgorithm AgrawalGoyalTS.TwoArmed
open scoped ENNReal

namespace KaufmannTS.Bernoulli

/-- §2, p. 3 (cited from [9]): the Bayes-UCB index is below the KL-UCB index, `q_{a,t} < u_{a,t}`,
for an arm with `S ≤ N` successes in `N` draws, at every paper round `1 ≤ t ≤ T` of a horizon
`T ≥ 3`. -/
theorem bayesucb_lt_klucb (T t S N : ℕ) (hT : 3 ≤ T) (ht : 1 ≤ t) (htT : t ≤ T) (hSN : S ≤ N) :
    bayesucbIdx T t S N < klucbIdx T t S N := by sorry

end KaufmannTS.Bernoulli
