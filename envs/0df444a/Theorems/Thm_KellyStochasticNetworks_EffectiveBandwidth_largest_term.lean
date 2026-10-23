-- Prove2me | Theorems.Thm_KellyStochasticNetworks_EffectiveBandwidth_largest_term
-- name    : KellyStochasticNetworks.EffectiveBandwidth.largest_term
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:48:11.324998+00:00
-- url     : https://prove2.me/theorems/2683d0eb-3a19-45b7-89ae-738d5a4470e3
-- title:
--   Exercise 6.9 — principle of the largest term
-- statement:
--   Let $(a_n)$ and $(b_n)$ be positive real sequences with finite real logarithmic rates $a$ and $b$, respectively, and suppose $a\ge b$. Then
--   $$\frac1n\log a_n\to a,\quad\frac1n\log b_n\to b\quad\Longrightarrow\quad\frac1n\log(a_n+b_n)\to a.$$
--   For any natural number $T$, let $p_n(0),\ldots,p_n(T)$ be positive real sequences with finite rates $r(0),\ldots,r(T)$. The finite-sum conclusion is
--   $$\frac1n\log\left(\sum_{t=0}^{T}p_n(t)\right)\longrightarrow\max_{0\le t\le T}r(t).$$
--   The item includes both assertions of the exercise. It is a finite-sum principle and supplies no countable-time upper bound.
--
--   **Formalization Note** The scale is $n=N+1$, and sequences are reindexed accordingly. Positivity makes the real logarithms genuine logarithms. The finite maximum is taken over the nonempty type $\operatorname{Fin}(T+1)$, including its one-element case $T=0$. The real limits are the finite-rate interpretation of the exercise's displayed limits.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 147 (PDF p. 155), Exercise 6.9; DOI https://doi.org/10.1017/CBO9781139565363

import Mathlib

open Filter Topology
open scoped BigOperators

namespace KellyStochasticNetworks.EffectiveBandwidth

theorem largest_term :
    (∀ (aSeq bSeq : ℕ → ℝ) (a b : ℝ),
      (∀ N, 0 < aSeq N) → (∀ N, 0 < bSeq N) → b ≤ a →
      Tendsto (fun N : ℕ => Real.log (aSeq N) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 a) →
      Tendsto (fun N : ℕ => Real.log (bSeq N) / ((N + 1 : ℕ) : ℝ)) atTop (𝓝 b) →
      Tendsto (fun N : ℕ => Real.log (aSeq N + bSeq N) / ((N + 1 : ℕ) : ℝ))
        atTop (𝓝 a)) ∧
    (∀ (T : ℕ) (p : Fin (T + 1) → ℕ → ℝ) (r : Fin (T + 1) → ℝ),
      (∀ t N, 0 < p t N) →
      (∀ t, Tendsto (fun N : ℕ => Real.log (p t N) / ((N + 1 : ℕ) : ℝ))
        atTop (𝓝 (r t))) →
      Tendsto (fun N : ℕ => Real.log (∑ t, p t N) / ((N + 1 : ℕ) : ℝ))
        atTop (𝓝 (Finset.univ.sup' Finset.univ_nonempty r))) := by sorry

end KellyStochasticNetworks.EffectiveBandwidth
