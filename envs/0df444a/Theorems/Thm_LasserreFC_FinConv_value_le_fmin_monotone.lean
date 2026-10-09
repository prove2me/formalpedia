-- Prove2me | Theorems.Thm_LasserreFC_FinConv_value_le_fmin_monotone
-- name    : LasserreFC.FinConv.value_le_fmin_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:33:32.429672+00:00
-- url     : https://prove2.me/theorems/dc24f867-7bbf-4710-8bef-52c22b9e6c75
-- title:
--   p. 2 — f_k ≤ f_min for all k, and {f_k} is monotonically increasing
-- statement:
--   Let $f_{\min}$ be the minimum value of (1.1), attained on the feasible set $K$, and let $f_k$ be the optimal value of the order-$k$ relaxation (1.2) of Lasserre's hierarchy. Then
--
--   $$f_k \le f_{\min} \quad\text{for all } k \in \mathbb N, \qquad f_0 \le f_1 \le f_2 \le \cdots.$$
--
--   Together with the feasibility of $\gamma = f_{\min} - \varepsilon$ at a fixed order (the $\varepsilon$-argument), this pins $f_k$ to $f_{\min}$ for all large $k$ in the proof of Theorem 1.1.
--
--   **Formalization Note** $f_k$ takes values in $[-\infty, +\infty]$ (`EReal`). The minimum value is given as a real number that is the least value of $f$ on $K$, which excludes only $K = \emptyset$; monotonicity holds without it.
-- source:
--   J. Nie, Optimality conditions and finite convergence of Lasserre's hierarchy, arXiv:1206.0319v2, p. 2, "Clearly, f_k ≤ f_min for all k and {f_k} is monotonically increasing"

import Mathlib
import Definitions.Def_LasserreFC_FinConv_Setting
import Definitions.Def_LasserreFC_FinConv_Hierarchy

namespace LasserreFC.FinConv

open MvPolynomial

/-- p. 2: `f_k ≤ f_min` for all `k`, and `{f_k}` is monotonically increasing. -/
theorem value_le_fmin_monotone {n m1 m2 : ℕ} (P : POP n m1 m2) (fmin : ℝ)
    (hfmin : IsLeast ((fun x => eval x P.f) '' P.K) fmin) :
    (∀ k : ℕ, lasserreValue P k ≤ (fmin : EReal)) ∧ Monotone (lasserreValue P) := by sorry

end LasserreFC.FinConv
