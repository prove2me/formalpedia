-- Prove2me | Theorems.Thm_MultiPriceOnline_Hardness_lemma_4_optimization
-- name    : MultiPriceOnline.Hardness.lemma_4_optimization
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T07:56:54.442964+00:00
-- url     : https://prove2.me/theorems/9ed0af3c-9f6d-42b5-b99f-6477fbe9ed41
-- title:
--   Proof of Lemma 4, pp. 47–48 — the constraints (46)–(47) bound the revenue (48) by (26) up to εnk
-- statement:
--   This is the optimization step in the proof of Lemma 4 (pp. 47–48, (49)). It turns the counting constraints (46)–(47) into the bound (26), with an error of order $o(nk)$.
--
--   Let $m\ge1$, let $0<r^{(1)}<\dots<r^{(m)}$ be a price set with booking limits $\alpha$ (Proposition 1), and let $B$ solve (24) with $B_1=1$ (Proposition 4). For $n$ groups, group $t\in\{0,\dots,n-1\}$ belongs to phase $j$ when $\lfloor(1-B_j)n\rfloor\le t<\lfloor(1-B_{j+1})n\rfloor$, with $B_{m+1}=0$. Fix $k\ge1$ and $\varepsilon>0$. Then there is $N_0$ such that for every $n\ge N_0$ and all reals $q_0,\dots,q_{n-1}$ with
--   $$q_t\ge0,\qquad \sum_{t=0}^{n-1}q_t\le k,\qquad (n-t)\,q_t\le k\quad(t<n),$$
--   we have
--   $$\sum_{t=0}^{n-1} r^{(\mathrm{phase}(t))}(n-t)\,q_t\ \le\ \max\Big\{\sum_{j=1}^m r^{(j)}B_j n\,(1-e^{-\lambda_j})\,k\Big\}+\varepsilon nk .$$
--   The maximum is over $\lambda$ with $\lambda_j\ge0$, $\lambda_j\le\ln(B_j/B_{j+1})$ for $j\in[m-1]$, and $\sum_j\lambda_j\le1$.
--
--   Combined with the counting bounds (46)–(48), this gives Lemma 4. Here $\lambda_j$ plays the role of $\frac1k\sum_{t\in\text{phase }j}q_t$.
--
--   **Formalization Note** The paper assumes $B_jn$ is an integer and replaces harmonic sums by logarithms "since $n\to\infty$"; the $\varepsilon nk$ term absorbs both approximations. The maximum is written as a real supremum, the same set as in Lemma 4. Groups are 0-based, so the paper's $n+1-t$ is $n-t$.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, App. D, proof of Lemma 4, pp. 46–48, eqs. (46)–(49)

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_Instance

namespace MultiPriceOnline.Hardness
open Finset
theorem lemma_4_optimization {m : ℕ} {r α B : ℕ → ℝ} (hm : 1 ≤ m) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (hB : IsPhaseB m r α B) (k : ℕ) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ q : ℕ → ℝ, (∀ t < n, 0 ≤ q t) → (∑ t ∈ range n, q t) ≤ k →
      (∀ t < n, ((n : ℝ) - t) * q t ≤ k) →
      ∑ t ∈ range n, r (phaseOf n m B t) * ((n : ℝ) - t) * q t
        ≤ sSup {v : ℝ | ∃ lam : ℕ → ℝ, (∀ j ∈ Icc 1 m, 0 ≤ lam j) ∧
                (∀ j ∈ Icc 1 (m - 1), lam j ≤ Real.log (B j / B (j + 1))) ∧
                (∑ j ∈ Icc 1 m, lam j) ≤ 1 ∧
                v = ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-lam j)) * k}
            + ε * n * k := by sorry
end MultiPriceOnline.Hardness
