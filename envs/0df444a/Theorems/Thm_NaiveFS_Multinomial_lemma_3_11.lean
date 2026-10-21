-- Prove2me | Theorems.Thm_NaiveFS_Multinomial_lemma_3_11
-- name    : NaiveFS.Multinomial.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:14:55.768736+00:00
-- url     : https://prove2.me/theorems/4d616491-166d-4bf2-8a40-d850402417a2
-- title:
--   Lemma 3.11, p. 15 — s_k(c) = min_{λ≥0} λk + Σᵢ max(0, cᵢ − λ) for c ≥ 0, with its LP dual (36)
-- statement:
--   Let $c\in\mathbb R^n_+$ and $k\in\mathbb N$, and let $s_k(c)$ be the sum of the $k$ largest entries of $c$.
--
--   1. **Variational form (35).**
--   $$s_k(c)=\min_{\lambda\ge0}\ \lambda k+\sum_{i=1}^n\max(0,c_i-\lambda),$$
--   and the minimum is attained.
--   2. **Optimal multipliers.** If $k\le n$, a value $\lambda\ge0$ attains the minimum exactly when $\lambda\in[c_{[k+1]},c_{[k]}]$, where $c_{[1]}\ge\dots\ge c_{[n]}$; equivalently $\#\{i:c_i>\lambda\}\le k\le\#\{i:c_i\ge\lambda\}$. At $k=0$ only the counting form is used.
--   3. **Dual LP (36).** The linear program $\max\{x^\top c:\ \mathbf 1^\top x\le k,\ x+z=\mathbf 1,\ x,z\ge0\}$ has optimal value $s_k(c)$.
--   4. If the $c_i$ are pairwise distinct, every optimal $x$ of (36) has at most one coordinate in $(0,1)$.
--   5. If moreover $k\ge1$ and $c_{[k]}>0$, every optimal $x$ of (36) is binary.
--
--   The variational form is what turns the dual of the sparse problem into the one-dimensional problem (USMNB), and the structure of optimal LP solutions is what bounds the number of fractional coordinates in the primalization of §3.7.
--
--   **Formalization Note** $s_k$ sums exactly $\min(k,n)$ entries; for $c\ge0$ this agrees with the maximum over subsets $|T|\le k$. The condition $\lambda\in[c_{[k+1]},c_{[k]}]$ is written without sorting, by counting; it is stated as an equivalence (the page asserts the direction "optimal $\Rightarrow$ in the interval"). The counting form also covers $k=0$: it says $\lambda\ge\max_i c_i$. In (36) $z$ is eliminated as $z=\mathbf 1-x$, so $x\in[0,1]^n$, and "$z$ has at most one nonbinary coefficient" is then the same statement as for $x$; $c_{[k]}>0$ is written $k\le\#\{i:c_i>0\}$.
-- source:
--   Askari, d'Aspremont & El Ghaoui, Naive Feature Selection, arXiv:1905.09884v4, p. 15, Lemma 3.11 (35)–(36)

import Mathlib
import Definitions.Def_NaiveFS_Multinomial_Model

open Finset

namespace NaiveFS.Multinomial

/-- Lemma 3.11, p. 15. For `c ∈ ℝⁿ₊`:
(a) `s_k(c) = min_{λ ≥ 0} λk + Σᵢ max(0, cᵢ − λ)` (35);
(b) for `k ≤ n`, `λ ≥ 0` attains (35) iff `λ ∈ [c_[k+1], c_[k]]`, written without sorting as
`#{i : λ < cᵢ} ≤ k ≤ #{i : λ ≤ cᵢ}`;
(c) the dual LP (36), with `z = 1 − x` eliminated, has optimal value `s_k(c)`;
(d) if the `cᵢ` are distinct, every optimal `x` of (36) has at most one coefficient in `(0,1)`;
(e) if moreover `c_[k] > 0` (i.e. `k ≤ #{i : cᵢ > 0}`, `k ≥ 1`), every optimal `x` is binary. -/
theorem lemma_3_11 {n : ℕ} (k : ℕ) (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    IsLeast {v | ∃ lam : ℝ, 0 ≤ lam ∧ v = lam * k + ∑ i, max 0 (c i - lam)} (topSum k c) ∧
    (k ≤ n → ∀ lam : ℝ, 0 ≤ lam →
      (lam * k + ∑ i, max 0 (c i - lam) = topSum k c ↔
        ((univ.filter (fun i => lam < c i)).card ≤ k ∧
          k ≤ (univ.filter (fun i => lam ≤ c i)).card))) ∧
    IsGreatest {v | ∃ x : Fin n → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) ∧ ∑ i, x i ≤ k ∧
      v = ∑ i, x i * c i} (topSum k c) ∧
    (Function.Injective c → ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → ∑ i, x i ≤ k →
      ∑ i, x i * c i = topSum k c →
      (univ.filter (fun i => 0 < x i ∧ x i < 1)).card ≤ 1) ∧
    (Function.Injective c → 1 ≤ k → k ≤ (univ.filter (fun i => 0 < c i)).card →
      ∀ x : Fin n → ℝ, (∀ i, 0 ≤ x i ∧ x i ≤ 1) → ∑ i, x i ≤ k →
      ∑ i, x i * c i = topSum k c → ∀ i, x i = 0 ∨ x i = 1) := by sorry

end NaiveFS.Multinomial
