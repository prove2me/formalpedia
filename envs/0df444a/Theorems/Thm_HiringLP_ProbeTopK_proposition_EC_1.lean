-- Prove2me | Theorems.Thm_HiringLP_ProbeTopK_proposition_EC_1
-- name    : HiringLP.ProbeTopK.proposition_EC_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:18.763551+00:00
-- url     : https://prove2.me/theorems/001be504-3847-404b-9192-5a86728e0596
-- title:
--   Proposition EC.1 (Yan 2011, Lemma 4.4) — the k-uniform weighted rank function has correlation gap ≤ (1 − e^{−k}k^k/k!)^{−1}
-- statement:
--   Let $n, k \ge 1$, let $w \in \mathbb{R}^n_{\ge 0}$ and let $w^*(D) = \max_{R \subseteq D, |R| \le k} \sum_{i \in R} w_i$ be the weighted rank function of the $k$-uniform matroid on $[n]$. Let $\mathcal D$ be any distribution on subsets of $[n]$, with marginals $q_i = \Pr_{D\sim\mathcal D}(i \in D)$, and let $\mathcal I(\mathcal D)$ be the distribution in which each $i$ is included independently with probability $q_i$. Then
--
--   $$
--   \Big(1 - \frac{e^{-k}k^k}{k!}\Big)\, \mathbb{E}_{D \sim \mathcal D}\, w^*(D) \;\le\; \mathbb{E}_{D \sim \mathcal I(\mathcal D)}\, w^*(D),
--   $$
--
--   that is, the correlation gap $\sup_{\mathcal D} \mathbb{E}_{\mathcal D} w^* / \mathbb{E}_{\mathcal I(\mathcal D)} w^*$ is at most $(1 - e^{-k}k^k/k!)^{-1}$.
--
--   This is the result of Yan (2011) on which the paper's constant rests: it converts a correlated benchmark (the LP) into an independent one (an algorithm) at the cost of the factor $1 - e^{-k}k^k/k!$, which is $1 - 1/e$ at $k = 1$ and tends to $1$ as $k \to \infty$.
--
--   **Formalization Note.** The ratio form is stated multiplicatively, which avoids $0/0$ when both expectations vanish and is equivalent otherwise. A distribution on subsets is a non-negative weight function $\mu$ on `Finset (Fin n)` with total mass $1$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. ec2 (PDF p. 34), App. A.1, Proposition EC.1 (citing Yan 2011, Lemma 4.4)

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_WeightedRank

namespace HiringLP.ProbeTopK

theorem proposition_EC_1 {n : ℕ} (k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    (μ : Finset (Fin n) → ℝ) (hμ0 : ∀ S, 0 ≤ μ S) (hμ1 : ∑ S, μ S = 1) :
    (1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ)) * ∑ S, μ S * wrank w k S ≤
      ∑ S, indepProb (marg μ) S * wrank w k S := by sorry

end HiringLP.ProbeTopK
