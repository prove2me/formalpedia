-- Prove2me | Theorems.Thm_MetodosNumericos_bisection_convergence
-- name    : MetodosNumericos.bisection_convergence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-20T16:39:46.393469+00:00
-- url     : https://prove2.me/theorems/b152db32-83d9-4631-bc73-8d9692cd1b8e
-- title:
--   Convergence and error bound of the bisection method
-- statement:
--   Let $f$ be continuous on $[a,b]$ with $a<b$, $f(a)<0$ and $f(b)>0$. Then there is a zero $\\bar{x} \\in [a,b]$ of $f$ such that, for every $n$: $\\bar{x}$ belongs to the $n$-th bisection bracket $[a_n,b_n]$; the bracket has width $b_n - a_n = (b-a)/2^n$; the approximation $x_{n+1} = (a_n+b_n)/2$ satisfies $|x_{n+1} - \\bar{x}| \\le (b-a)/2^n$; and $x_{n+1} \\to \\bar{x}$. These are items (i)–(iv) of Proposição 3.2.1.
-- source:
--   S. R. Freitas, Métodos Numéricos (UFMS, 2000), Cap. 3, Proposição 3.2.1, pp. 39–40 (items i–iv).

import Mathlib
import Definitions.Def_MetodosNumericos_zerosDefs

open Filter Topology

namespace MetodosNumericos

theorem bisection_convergence (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ r ∈ Set.Icc a b, f r = 0 ∧
      (∀ n : ℕ, r ∈ Set.Icc (bisect f a b n).1 (bisect f a b n).2) ∧
      (∀ n : ℕ, (bisect f a b n).2 - (bisect f a b n).1 = (b - a) / 2 ^ n) ∧
      (∀ n : ℕ, |bisectMid f a b n - r| ≤ (b - a) / 2 ^ n) ∧
      Tendsto (bisectMid f a b) atTop (𝓝 r) := by sorry

end MetodosNumericos
