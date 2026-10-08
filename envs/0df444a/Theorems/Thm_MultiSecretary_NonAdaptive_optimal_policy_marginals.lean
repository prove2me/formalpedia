-- Prove2me | Theorems.Thm_MultiSecretary_NonAdaptive_optimal_policy_marginals
-- name    : MultiSecretary.NonAdaptive.optimal_policy_marginals
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:26:23.830707+00:00
-- url     : https://prove2.me/theorems/11f471e9-6feb-44c3-aa06-68507daa98d0
-- title:
--   Lemma 7 — an optimal non-adaptive policy has f₁/2 ≤ qₜ ≤ 1 − fₘ/2 in all but 2M√n periods, so ς² ≥ (f₁fₘ/4)(n − 2M√n)
-- statement:
--   Let $0<a_m<\dots<a_1$, let $\epsilon>0$, and consider masses $f_j>0$ summing to one with $\epsilon=\tfrac12\min_jf_j$. There is a constant $M=M(\epsilon,m,a_1,\dots,a_m)<\infty$ such that, whenever $(f_1+\epsilon)n\le k\le(1-f_m-\epsilon)n$:
--
--   1. an optimal non-adaptive policy exists (one with $V^\pi_{\mathrm{on}}(n,k)=V^*_{\mathrm{na}}(n,k)$);
--   2. every optimal non-adaptive policy $\pi$, with marginal selection probabilities $q_t=\sum_jp_{j,t}f_j$, satisfies
--   $$\sum_{t\in[n]}\mathbb 1\Big\{q_t\ge\frac{f_1}2\Big\}\ge n-M\sqrt n\quad\text{and}\quad\sum_{t\in[n]}\mathbb 1\Big\{1-q_t\ge\frac{f_m}2\Big\}\ge n-M\sqrt n;$$
--   consequently
--   $$\sum_{t\in[n]}\mathbb 1\Big\{q_t\ge\frac{f_1}2,\ 1-q_t\ge\frac{f_m}2\Big\}\ge n-2M\sqrt n,\qquad \varsigma^2(\pi)=\sum_{t\in[n]}q_t(1-q_t)\ge\frac{f_1f_m}4(n-2M\sqrt n).$$
--
--   An optimal non-adaptive policy selects with a probability bounded away from $0$ and $1$ in most periods, so its number of selections has variance of order $n$; combined with Lemma 5 this drives the $\sqrt n$ lower bound of Theorem 3.
--
--   **Formalization Note** Lean index $j\in\{0,\dots,m-1\}$ is the paper's index $j+1$, so `a 0` is the largest value $a_1$, `f 0` is $f_1$ and `f (Fin.rev 0)` is $f_m$. The paper's "an optimal non-adaptive policy must satisfy" presupposes that one exists; the existence is stated as a conjunct so that the universal part cannot hold vacuously. The paper names $M\equiv M(\epsilon,a_1,a_2,a_m)$; the constant is chosen after $\epsilon$, $m$ and all of $a$, and before $f$, $n$, $k$, because the paper's argument for the right inequality of (36) (p. 38) does not go through as printed and a correct argument also uses $a_{m-1}$.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Lemma 7, eq. (36), p. 27 (proof pp. 37–38)

import Mathlib
import Definitions.Def_MultiSecretary_NonAdaptive_Model
import Definitions.Def_MultiSecretary_NonAdaptive_Policy

namespace MultiSecretary.NonAdaptive

open Finset

/-- Lemma 7 (p. 27): with `ϵ = ½ min f_j` and `(f_1 + ϵ) n ≤ k ≤ (1 - f_m - ϵ) n`, an optimal
non-adaptive policy exists, and every optimal one has `q_t ≥ f_1/2` and `1 - q_t ≥ f_m/2` in all but
`M√n` periods each (36), both in all but `2M√n` periods, and `ς² ≥ (f_1 f_m/4)(n - 2M√n)`. -/
theorem optimal_policy_marginals (ε : ℝ) (hε : 0 < ε) (m : ℕ) [NeZero m] (a : Fin m → ℝ)
    (ha : IsValues a) :
    ∃ M : ℝ, ∀ f : Fin m → ℝ, IsMasses f → eps f = ε → ∀ n k : ℕ,
      (f 0 + ε) * n ≤ k → (k : ℝ) ≤ (1 - f (Fin.rev 0) - ε) * n →
      (∃ p : Fin m → Fin n → ℝ, IsNAPolicy p ∧ Vna a f k p = VstarNa a f n k) ∧
      ∀ p : Fin m → Fin n → ℝ, IsNAPolicy p → Vna a f k p = VstarNa a f n k →
        ((n : ℝ) - M * Real.sqrt n ≤
            ((univ.filter (fun t => f 0 / 2 ≤ selProb f p t)).card : ℝ) ∧
          (n : ℝ) - M * Real.sqrt n ≤
            ((univ.filter (fun t => f (Fin.rev 0) / 2 ≤ 1 - selProb f p t)).card : ℝ)) ∧
        (n : ℝ) - 2 * M * Real.sqrt n ≤
            ((univ.filter (fun t => f 0 / 2 ≤ selProb f p t ∧
              f (Fin.rev 0) / 2 ≤ 1 - selProb f p t)).card : ℝ) ∧
        f 0 * f (Fin.rev 0) / 4 * ((n : ℝ) - 2 * M * Real.sqrt n) ≤
          varSum (selProb f p) := by sorry

end MultiSecretary.NonAdaptive
