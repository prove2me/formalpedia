-- Prove2me | Theorems.Thm_MultiSecretary_NonAdaptive_sqrt_regret_lower_bound
-- name    : MultiSecretary.NonAdaptive.sqrt_regret_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:26:42.103382+00:00
-- url     : https://prove2.me/theorems/089762e0-f361-4727-97f0-8f8b73a0f745
-- title:
--   Theorem 3 — for (f₁ + ϵ)n ≤ k ≤ (1 − fₘ − ϵ)n, every non-adaptive policy has regret at least M√n
-- statement:
--   Let $0<a_m<a_{m-1}<\dots<a_1$ and $\epsilon>0$. There is a constant $M=M(\epsilon,m,a_1,\dots,a_m)>0$ such that for all masses $f_j>0$ summing to one with $\epsilon=\tfrac12\min\{f_m,\dots,f_1\}$ and all $(n,k)$ with $(f_1+\epsilon)n\le k\le(1-f_m-\epsilon)n$,
--   $$M\sqrt n\le V^*_{\mathrm{off}}(n,k)-V^*_{\mathrm{na}}(n,k).$$
--
--   When the budget is a fraction of $n$ bounded away from $f_1$ and from $1-f_m$, even the best non-adaptive policy loses order $\sqrt n$ against the offline optimum, while adaptive policies (the Budget-Ratio policy of the same paper) achieve regret bounded uniformly in $n$ and $k$.
--
--   **Formalization Note** Lean index $j\in\{0,\dots,m-1\}$ is the paper's index $j+1$, so `a 0` is the largest value $a_1$, `f 0` is $f_1$ and `f (Fin.rev 0)` is $f_m$. The constant is chosen after $\epsilon$, $m$, $a$ and before $f$, $n$, $k$, and it is required to be strictly positive (with $M=0$ the claim would reduce to $V^*_{\mathrm{na}}\le V^*_{\mathrm{off}}$). The statement holds for all $n$ in the range, as printed, with no threshold on $n$. The range is empty unless $f_1+f_m+2\epsilon\le1$, so the statement has content only for $m\ge3$.
-- source:
--   Arlotto, Gurvich, Uniformly Bounded Regret in the Multi-Secretary Problem, arXiv:1710.07719v2, Theorem 3, p. 25 (= Theorem 1, second display, p. 5)

import Mathlib
import Definitions.Def_MultiSecretary_NonAdaptive_Model
import Definitions.Def_MultiSecretary_NonAdaptive_Policy

namespace MultiSecretary.NonAdaptive

open Finset

/-- Theorem 3 (p. 25): for `ϵ = ½ min f_j` and `(f_1 + ϵ) n ≤ k ≤ (1 - f_m - ϵ) n` there is a constant
`M ≡ M(ϵ, m, a_1, …, a_m) > 0` with `M√n ≤ V*_off(n, k) - V*_na(n, k)`. -/
theorem sqrt_regret_lower_bound (ε : ℝ) (hε : 0 < ε) (m : ℕ) [NeZero m] (a : Fin m → ℝ)
    (ha : IsValues a) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : Fin m → ℝ, IsMasses f → eps f = ε → ∀ n k : ℕ,
      (f 0 + ε) * n ≤ k → (k : ℝ) ≤ (1 - f (Fin.rev 0) - ε) * n →
      M * Real.sqrt n ≤ Voff a f n k - VstarNa a f n k := by sorry

end MultiSecretary.NonAdaptive
