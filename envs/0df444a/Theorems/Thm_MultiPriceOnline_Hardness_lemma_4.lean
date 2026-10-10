-- Prove2me | Theorems.Thm_MultiPriceOnline_Hardness_lemma_4
-- name    : MultiPriceOnline.Hardness.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:37.062584+00:00
-- url     : https://prove2.me/theorems/ff7068cd-39bf-4908-b7d0-9df16d0fd8f7
-- title:
--   Lemma 4, p. 24 — online revenue on the counterexample is at most the maximum of (26), up to εnk
-- statement:
--   Let $m \ge 1$, let $0 < r^{(1)} < \dots < r^{(m)}$ be a price set with booking limits $\alpha$, let $B_1 = 1 > B_2 > \dots > B_m > 0$ solve (24), and set $B_{m+1} = 0$. Fix $k \ge 1$. For every $\varepsilon > 0$ there is $N_0$ such that for every $n \ge N_0$ the following holds. Let $\mathrm{alg}$ be any randomized online algorithm: a measurable random choice of a deterministic online algorithm, on any probability space. Run it on the counterexample of §5 with $n$ items, inventory $k$, and a uniformly random permutation $\pi$. Its expected revenue satisfies
--
--   $$\frac{1}{n!} \sum_{\pi} \mathbb E\big[\mathrm{ALG}(\mathcal S, \mathcal A_\pi)\big] \le \max\Big\{ \sum_{j=1}^m r^{(j)} B_j n (1 - e^{-\lambda_j}) k \Big\} + \varepsilon n k. \qquad (26)$$
--
--   The maximum is over $\lambda$ with $0 \le \lambda_j \le \ln(B_j / B_{j+1})$ for $j \in [m-1]$, $0 \le \lambda_m$, and $\sum_{j=1}^m \lambda_j \le 1$.
--
--   This is the upper bound on online algorithms that Lemma 5 then evaluates.
--
--   **Formalization Note** The paper states Lemma 4 without the error term. Its proof treats $\tau n$ as an integer and replaces harmonic sums by logarithms "since $n \to \infty$" (pp. 23, 47). It therefore establishes the bound only up to $o(nk)$, and the statement is the corresponding $\varepsilon$-form. The maximum is a real supremum of a set that is nonempty ($\lambda = 0$, since the $B_j$ decrease) and bounded above, so it is attained. Measurability of the revenue in $\omega$ is assumed. The revenue is bounded, so it is then integrable; without measurability the Bochner integral would be $0$ and the bound trivially true.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 24, Lemma 4, eq. (26); proof pp. 46–48, App. D

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_Model
import Definitions.Def_MultiPriceOnline_Hardness_Instance

namespace MultiPriceOnline.Hardness
open Finset MeasureTheory
theorem lemma_4 {m : ℕ} {r α B : ℕ → ℝ} (hm : 1 ≤ m) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (hB : IsPhaseB m r α B) (k : ℕ) (hk : 1 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (alg : Ω → OnlineAlg n),
        (∀ π : Equiv.Perm (Fin n),
          Measurable (fun ω => revenue k m r (alg ω) (hardInstance n k m B π))) →
        ((Nat.factorial n : ℝ))⁻¹ * ∑ π : Equiv.Perm (Fin n),
            ∫ ω, revenue k m r (alg ω) (hardInstance n k m B π) ∂μ
          ≤ sSup {v : ℝ | ∃ lam : ℕ → ℝ, (∀ j ∈ Icc 1 m, 0 ≤ lam j) ∧
                (∀ j ∈ Icc 1 (m - 1), lam j ≤ Real.log (B j / B (j + 1))) ∧
                (∑ j ∈ Icc 1 m, lam j) ≤ 1 ∧
                v = ∑ j ∈ Icc 1 m, r j * B j * n * (1 - Real.exp (-lam j)) * k}
            + ε * n * k := by sorry
end MultiPriceOnline.Hardness
