-- Prove2me | Theorems.Thm_OfflineStochMatch_Attenuation_lemma_4
-- name    : OfflineStochMatch.Attenuation.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:27.077976+00:00
-- url     : https://prove2.me/theorems/70634e6b-8530-435a-a944-960c53fe411b
-- title:
--   Lemma 4 (Baveja et al.), p. 12 — Pr[Σ B_i < t] ≥ Pr[Pois(µ) < t] when µ < t − 1
-- statement:
--   Fix an integer $t \ge 1$. Let $B_1, \dots, B_k$ be independent Bernoulli random variables with $\Pr[B_i = 1] = q_i \in [0,1]$, and let $\mu = \sum_{i=1}^k q_i$. If $\mu < t - 1$, then
--   $$\Pr\Bigl[\sum_{i=1}^k B_i < t\Bigr] \;\ge\; \Pr[\mathrm{Pois}(\mu) < t] = \sum_{i=0}^{t-1} \frac{e^{-\mu} \mu^i}{i!}.$$
--
--   The lemma compares the lower tail of a sum of independent Bernoullis with that of a Poisson variable of the same mean. In the analysis of Theorem 1 it bounds the probability that a vertex has not run out of patience before $e$ arrives (bound (9)).
--
--   **Formalization Note** The page prints $e^{-x\mu}$ in the Poisson sum; there is no $x$ in the lemma, and the Poisson cdf is $\sum_i e^{-\mu}\mu^i/i!$, which is what is stated. The probability is the finite sum, over the $2^k$ outcomes, of the product of the Bernoulli weights. At $t = 1$ the hypothesis $\mu < 0$ cannot hold, so that case is vacuous, as on the page.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 12, Lemma 4 (cited from Baveja et al., Algorithmica 2018)

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation

theorem lemma_4 (t k : ℕ) (q : Fin k → ℝ) (ht : 1 ≤ t) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (hμ : ∑ i, q i < (t : ℝ) - 1) :
    ∑ i ∈ Finset.range t, Real.exp (-(∑ j, q j)) * (∑ j, q j) ^ i / (i.factorial : ℝ)
      ≤ ∑ b : Fin k → Bool,
          coinWeight q b * (if (Finset.univ.filter (fun i => b i = true)).card < t then 1 else 0) := by sorry

end OfflineStochMatch.Attenuation
