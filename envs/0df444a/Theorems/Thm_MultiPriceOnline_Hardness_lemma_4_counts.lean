-- Prove2me | Theorems.Thm_MultiPriceOnline_Hardness_lemma_4_counts
-- name    : MultiPriceOnline.Hardness.lemma_4_counts
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T07:56:50.196144+00:00
-- url     : https://prove2.me/theorems/a986a3e9-d1a2-4942-996c-f51b5f920c0c
-- title:
--   Proof of Lemma 4, pp. 46–47 — counting bounds (46), (47) and revenue (48) for a deterministic online algorithm
-- statement:
--   This is the counting step in the proof of Lemma 4 (inequalities (46), (47) and the revenue expression (48)), stated for a single deterministic online algorithm.
--
--   Let $0<r^{(1)}<\dots<r^{(m)}$ be a price set and let $B_1,\dots,B_m$ be any reals. Consider the counterexample of §5 with $n\ge 1$ items, each with inventory $k$, and arrival sequence $\mathcal A_\pi$ for a permutation $\pi$ of the items. There are $nk$ customers, split into groups $t=0,\dots,n-1$ of $k$ consecutive customers each. Group $t$ is interested only in the items $\pi_t,\pi_{t+1},\dots,\pi_{n-1}$, at any price $r^{(j)}$ with $j\le \mathrm{phase}(t)$. Fix a deterministic online algorithm $\mathrm{ALG}$.
--
--   Then there are numbers $q_0,\dots,q_{n-1}$ with:
--
--   1. $q_t\ge 0$ for all $t<n$;
--   2. $\displaystyle\sum_{t=0}^{n-1} q_t\le k$ (the inventory of item $\pi_{n-1}$, (46));
--   3. $(n-t)\,q_t\le k$ for all $t<n$ (the size of group $t$, (47));
--   4. the revenue averaged over a uniformly random $\pi$ satisfies
--   $$\frac{1}{n!}\sum_{\pi}\mathrm{ALG}(\mathcal S,\mathcal A_\pi)\ \le\ \sum_{t=0}^{n-1} r^{(\mathrm{phase}(t))}\,(n-t)\,q_t .\qquad(48)$$
--
--   In the paper $q_t$ is the expected number of group-$t$ customers that buy item $\pi_i$, which by symmetry is the same for every $i\ge t$. Together with the optimization step this yields Lemma 4.
--
--   **Formalization Note** Groups and positions are 0-based, so the paper's $n+1-t$ becomes $n-t$. The statement is for one deterministic algorithm; the randomized case of Lemma 4 follows by integrating over the algorithm's randomness. The bound in item 4 is an inequality because a sale may happen at a price below $r^{(\mathrm{phase}(t))}$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, App. D, proof of Lemma 4, pp. 46–48, eqs. (46)–(48)

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_Model
import Definitions.Def_MultiPriceOnline_Hardness_Instance

namespace MultiPriceOnline.Hardness
open Finset
theorem lemma_4_counts {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (B : ℕ → ℝ) (n k : ℕ) (hn : 1 ≤ n) (alg : OnlineAlg n) :
    ∃ q : ℕ → ℝ, (∀ t < n, 0 ≤ q t) ∧ (∑ t ∈ range n, q t) ≤ k ∧
      (∀ t < n, ((n : ℝ) - t) * q t ≤ k) ∧
      ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n), revenue k m r alg (hardInstance n k m B π)
        ≤ ∑ t ∈ range n, r (phaseOf n m B t) * ((n : ℝ) - t) * q t := by sorry
end MultiPriceOnline.Hardness
