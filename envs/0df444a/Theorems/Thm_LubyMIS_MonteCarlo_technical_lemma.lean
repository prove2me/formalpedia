-- Prove2me | Theorems.Thm_LubyMIS_MonteCarlo_technical_lemma
-- name    : LubyMIS.MonteCarlo.technical_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T22:50:37.930961+00:00
-- url     : https://prove2.me/theorems/9bff316e-6c80-490e-867d-22ecc4090f63
-- title:
--   TECHNICAL LEMMA — max{γ_l : 1 ≤ l ≤ n} ≥ ½·min{α_n, 1/c}
-- statement:
--   Let $n \ge 1$, let $p_1 \ge p_2 \ge \dots \ge p_n \ge 0$ be real numbers and let $c > 0$. For $1 \le l \le n$ put
--   $$\alpha_l = \sum_{j=1}^{l} p_j, \qquad \beta_l = \sum_{j=1}^{l} \sum_{k=j+1}^{l} p_j p_k, \qquad \gamma_l = \alpha_l - c\,\beta_l .$$
--   Then
--   $$\max\{\gamma_l : 1 \le l \le n\} \;\ge\; \tfrac12 \min\Big\{\alpha_n, \frac1c\Big\}.$$
--
--   The quantity $\gamma_l$ is the second Bonferroni lower bound for the probability of a union of $l$ events with probabilities $p_1, \dots, p_l$ whose pairwise intersections have probability at most $c\,p_jp_k$. The lemma turns that bound into a lower bound for the union in terms of the total mass $\alpha_n$; it is used with $c = 2$ in Lemma A and $c = 1$ in Lemma B.
--
--   **Formalization Note** The sequence is a function $p : \mathbb{N} \to \mathbb{R}$ of which only $p_1, \dots, p_n$ matter; "$p_1 \ge \dots \ge p_n \ge 0$" is stated as antitonicity on $\{1, \dots, n\}$ together with $p_n \ge 0$. The maximum over $1 \le l \le n$ is expressed as the existence of such an $l$.
-- source:
--   Luby, A Simple Parallel Algorithm for the Maximal Independent Set Problem, SIAM J. Comput. 15(4), 1986, p. 1043, TECHNICAL LEMMA

import Mathlib

namespace LubyMIS.MonteCarlo

/-- TECHNICAL LEMMA (Luby 1986, §3.4, p. 1043). Let `p₁ ≥ ⋯ ≥ pₙ ≥ 0` and `c > 0`. With
`α_l = ∑_{j=1}^{l} p_j`, `β_l = ∑_{j=1}^{l} ∑_{k=j+1}^{l} p_j p_k`, `γ_l = α_l − c β_l`, some
`1 ≤ l ≤ n` has `γ_l ≥ ½ · min {α_n, 1/c}`. -/
theorem technical_lemma (n : ℕ) (hn : 1 ≤ n) (p : ℕ → ℝ)
    (hanti : ∀ j k : ℕ, 1 ≤ j → j ≤ k → k ≤ n → p k ≤ p j) (hpn : 0 ≤ p n)
    (c : ℝ) (hc : 0 < c) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ n ∧
      (∑ j ∈ Finset.Icc 1 l, p j) - c * (∑ j ∈ Finset.Icc 1 l, ∑ k ∈ Finset.Ioc j l, p j * p k)
        ≥ 1 / 2 * min (∑ j ∈ Finset.Icc 1 n, p j) (1 / c) := by sorry

end LubyMIS.MonteCarlo
