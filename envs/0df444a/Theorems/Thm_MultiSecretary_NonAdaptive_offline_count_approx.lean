-- Prove2me | Theorems.Thm_MultiSecretary_NonAdaptive_offline_count_approx
-- name    : MultiSecretary.NonAdaptive.offline_count_approx
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:03:49.848738+00:00
-- url     : https://prove2.me/theorems/85d9dadd-ee9c-4f01-b435-dcfb7869b3e1
-- title:
--   Lemma 8 — E[𝔖ⁿⱼ] = min{E[Zⁿⱼ], (k − Σ_{i<j} E[Zⁿᵢ])₊} ± M√n = s*ⱼ ± M√n
-- statement:
--   Let $0<a_m<\dots<a_1$ and $\epsilon>0$. There is a constant $M=M(\epsilon,m,a_m,\dots,a_1)$ such that for all masses $f_j>0$ summing to one with $\tfrac12\min_jf_j=\epsilon$, all $0\le k\le n$ and all $j\in[m]$,
--   $$\mathbb E[\mathfrak S^n_j]=\mathbb E\Big[\min\Big\{Z^n_j,\Big(k-\sum_{i<j}Z^n_i\Big)_+\Big\}\Big]=\min\Big\{\mathbb E[Z^n_j],\Big(k-\sum_{i<j}\mathbb E[Z^n_i]\Big)_+\Big\}\pm M\sqrt n,$$
--   and in turn $\mathbb E[\mathfrak S^n_j]=s^*_j\pm M\sqrt n$.
--
--   The expected offline counts are within $O(\sqrt n)$ of the solution of the deterministic relaxation; this is the step behind Proposition 6.
--
--   **Formalization Note** "$x=y\pm M\sqrt n$" is $|x-y|\le M\sqrt n$. The first equality is the definition (3) of $\mathfrak S^n_j$. $M$ is chosen after $\epsilon$, $m$, $a$ and before $f$, $n$, $k$, $j$.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Lemma 8, p. 40

import Mathlib
import Definitions.Def_MultiSecretary_NonAdaptive_Model

namespace MultiSecretary.NonAdaptive

open Finset

/-- Lemma 8 (p. 40): there is `M ≡ M(ϵ, m, a)` such that for all `j`,
`E[𝔖^n_j] = min{E[Z^n_j], (k - ∑_{i<j} E[Z^n_i])_+} ± M√n`, and in turn `E[𝔖^n_j] = s*_j ± M√n`. -/
theorem offline_count_approx (ε : ℝ) (hε : 0 < ε) (m : ℕ) [NeZero m] (a : Fin m → ℝ)
    (ha : IsValues a) :
    ∃ M : ℝ, ∀ f : Fin m → ℝ, IsMasses f → eps f = ε → ∀ n k : ℕ, k ≤ n → ∀ j : Fin m,
      |expect f (fun x : Fin n → Fin m => (offCount k x j : ℝ)) -
          min (expect f (fun x : Fin n → Fin m => (count x n j : ℝ)))
            (max 0 ((k : ℝ) - ∑ i ∈ univ.filter (fun i : Fin m => i < j),
              expect f (fun x : Fin n → Fin m => (count x n i : ℝ))))| ≤ M * Real.sqrt n ∧
      |expect f (fun x : Fin n → Fin m => (offCount k x j : ℝ)) - sStar f n k j| ≤
        M * Real.sqrt n := by sorry

end MultiSecretary.NonAdaptive
