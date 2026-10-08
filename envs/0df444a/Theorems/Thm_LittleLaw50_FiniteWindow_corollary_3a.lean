-- Prove2me | Theorems.Thm_LittleLaw50_FiniteWindow_corollary_3a
-- name    : LittleLaw50.FiniteWindow.corollary_3a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:55.725439+00:00
-- url     : https://prove2.me/theorems/7211515b-56b2-4c99-b26c-99dfd7a76264
-- title:
--   §2.2.3, Corollary (3)(a), p. 539 — L_k = λ_k W_k for every class k of items
-- statement:
--   Consider one sample path observed over $[0, T]$ with $0 < T < \infty$, items $i = 1, \dots, M$ with arrival times $a_i$ and departure times $d_i \ge a_i$, possibly present at $0$ and at $T$. The items are divided into mutually exclusive classes $k = 1, \dots, K$ by a class assignment $c$. For a class $k$, let $L_k$, $\lambda_k$, $W_k$ be the LL parameters computed from the class-$k$ items alone: $L_k = A_k/T$ with $A_k = \int_0^T n_k(t)\,dt$ and $n_k(t)$ the number of class-$k$ items in the system at $t$; $\lambda_k = S_k(T)/T$ with $S_k(T)$ the number of class-$k$ items in the system over $[0, T]$; and $W_k$ the average over those $S_k(T)$ items of their time in the system during $[0, T]$. Then for every class $k$,
--
--   $$L_k = \lambda_k W_k.$$
--
--   Little's Law therefore holds for each market segment separately, which is how it is applied to multiclass systems in practice.
--
--   **Formalization Note** The class assignment is a function from items to $\{1, \dots, K\}$, which makes the classes disjoint and exhaustive. The conventions are those of Theorem LL.2: half-open presence, truncated times in window, and Lean's value $0$ for $W_k$ when $S_k(T) = 0$ (then both sides are $0$).
-- source:
--   Little, Little's Law as Viewed on Its 50th Anniversary, Oper. Res. 59(3) (2011), DOI 10.1287/opre.1110.0940, p. 539, §2.2.3, Corollary (3)(a)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_LittleLaw50_FiniteWindow_Window

namespace LittleLaw50.FiniteWindow

/-- **§2.2.3, Corollary (3)(a)** (Little 2011, p. 539). Items are split into `K` mutually
exclusive classes by `c`. For every class `k`, the LL parameters computed from the class-`k`
items alone satisfy `L_k = λ_k W_k`. -/
theorem corollary_3a {M K : ℕ} (a d : Fin M → ℝ) (c : Fin M → Fin K) (T : ℝ) (hT : 0 < T)
    (had : ∀ i, a i ≤ d i) (k : Fin K) :
    Lw (classItems c k) a d T
      = lamw (classItems c k) a d T * Ww (classItems c k) a d T := by sorry

end LittleLaw50.FiniteWindow
