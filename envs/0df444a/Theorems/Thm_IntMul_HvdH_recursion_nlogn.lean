-- Prove2me | Theorems.Thm_IntMul_HvdH_recursion_nlogn
-- name    : IntMul.HvdH.recursion_nlogn
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T14:07:21.074883+00:00
-- url     : https://prove2.me/theorems/41e9050e-518a-4938-b747-f7c8529da02c
-- title:
--   Closing an n log n recursion with contraction ρ < 1
-- statement:
--   Let $L:\mathbb N\to\mathbb R$ satisfy $L(n)\ge1$ and let $M:\mathbb N\to\mathbb R$. Fix $K\ge0$, $\rho<1$ and $n_0$. Suppose that for every $n\ge\max(n_0,1)$ there are finitely many pairs $(c_i,m_i)$ with $c_i\ge0$ and $1\le m_i<n$ such that
--   $$\sum_i c_i\,m_i\,L(m_i)\le\rho\,n\,L(n)\qquad\text{and}\qquad M(n)\le\sum_i c_i\,M(m_i)+K\,n\,L(n).$$
--   Then there is a constant $C\ge0$ with $M(n)\le C\,n\,L(n)$ for all $n\ge1$.
--
--   With $L=\lg$, this is the recursion-closing step of Harvey–van der Hoeven (§5). The recursive calls of the $d$-dimensional algorithm cost at most a fixed fraction $\rho<1$ of $n\lg n$ (there $\rho\approx 1728/d$). All non-recursive work costs $O(n\lg n)$. Together these give $M(n)=O(n\lg n)$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, §5 (proof of Theorem 1.1)

import Mathlib

namespace IntMul.HvdH
theorem recursion_nlogn (M : ℕ → ℝ) (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (n₀ : ℕ) (K ρ : ℝ)
    (hK : 0 ≤ K) (hρ : ρ < 1)
    (step : ∀ n, n₀ ≤ n → 1 ≤ n → ∃ l : List (ℝ × ℕ),
      (∀ q ∈ l, 0 ≤ q.1 ∧ 1 ≤ q.2 ∧ q.2 < n) ∧
      (l.map (fun q => q.1 * (q.2 * L q.2))).sum ≤ ρ * (n * L n) ∧
      M n ≤ (l.map (fun q => q.1 * M q.2)).sum + K * (n * L n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, 1 ≤ n → M n ≤ C * (n * L n) := by sorry
end IntMul.HvdH
