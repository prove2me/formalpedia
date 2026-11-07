-- Prove2me | Theorems.Thm_MinSumClust_lemma_49
-- name    : MinSumClust.lemma_49
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:08.076245+00:00
-- url     : https://prove2.me/theorems/50a05948-364e-47ad-b1ae-de1566fbcd4d
-- title:
--   Lemma 49 — given the labelings, Algorithm 6 opens every residual $S_2$ with probability at least $1-3\alpha$
-- statement:
--   Let $\mathcal S_1,\mathcal S_2$ be partitions of $D$ into $k_1$ and $k_2$ clusters with $k_1\le k<k_2$, and $\alpha=(k_2-k)/(k_2-k_1)$. Fix labelings $\ell_M,\ell_L$ that the sampling of §5.3 can produce and run Algorithm 5. Then for every $S_2\in\mathcal S_2^{(\mathrm{res})}$ and every tie-breaking order of Algorithm 6,
--
--   $$\Pr\bigl[S_2\in\mathcal S_{2,O}^{(\mathrm{res})}\ \big|\ \ell_M,\ell_L\bigr]\ \ge\ 1-3\alpha,$$
--
--   the probability being over the random choices of Algorithm 6. It implies that every $S_2$ cluster is closed with probability $O(\alpha)$ (Observation 51), the key to the cost bounds of §5.5.
--
--   Differences from the source:
--
--   - reading: conditioning on ℓ_M, ℓ_L → for every pair of labelings in the support of the §5.3 sampling, the probability under Algorithm 6 alone; reason: conditioning on a discrete random variable fixes one of its values
--   - generalization: §5 assumes α ≤ 1/2 w.l.o.g. (p.42) → no assumption on α; reason: for α ≥ 1/3 the bound is trivial, and the argument for α < 1/3 does not use it; the paper's case is included
--   - encoding: ties broken arbitrarily → a ranking parameter rk, every rk; reason: same orders
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 49, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_MinSumClust_pexp
import Definitions.Def_MinSumClust_Bipoint
import Definitions.Def_MinSumClust_alg5
import Definitions.Def_MinSumClust_alg6

namespace MinSumClust

/-- **Lemma 49**, p.45 (PDF p.47).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 49, p.45.

Let `𝒮₁, 𝒮₂` be partitions of `D` into `k₁` and `k₂` clusters, `k₁ ≤ k < k₂`, and
`α = (k₂ − k)/(k₂ − k₁)`. Conditioning on `ℓ_M, ℓ_L`, every `S₂ ∈ 𝒮₂^(res)` is opened by
Algorithm 6 with probability at least `1 − 3α`:
`Pr[S₂ ∈ 𝒮₂,O^(res) | ℓ_M, ℓ_L] ≥ 1 − 3α`.

**Formalization Note.** Conditioning on the labelings is fixing a pair `ℓ` that §5.3 can produce
(`ValidLabels`); the probability is over Algorithm 6 alone, for every tie ranking `rk`. The
section's standing "w.l.o.g. α ≤ 1/2" (p.42) is not assumed: for `α ≥ 1/3` the bound is trivial. -/
theorem lemma_49 {D : Type} [Fintype D] [DecidableEq D]
    (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (k : ℕ) (hk₁ : S₁.parts.card ≤ k)
    (hk₂ : k < S₂.parts.card) (rk : Finset D → ℕ) (ℓ : Labels D) (hℓ : ValidLabels S₁ S₂ ℓ) :
    ∀ T ∈ (alg5 S₁ S₂ ℓ).res2,
      1 - 3 * alphaBip S₁ S₂ k ≤ pprob (alg6 S₁ S₂ k rk ℓ (alg5 S₁ S₂ ℓ)) (fun o => T ∈ o.open2) := by sorry

end MinSumClust
