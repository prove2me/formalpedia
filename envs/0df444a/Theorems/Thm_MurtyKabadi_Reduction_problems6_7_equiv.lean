-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_problems6_7_equiv
-- name    : MurtyKabadi.Reduction.problems6_7_equiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:14:39.643755+00:00
-- url     : https://prove2.me/theorems/488bf379-b46b-40fa-aaab-84649de30373
-- title:
--   Proof of Theorem 1, p. 125 — Problems 6 and 7 are equivalent
-- statement:
--   Let $d_0; d_1, \dots, d_n$ be positive integers and $\delta$ an integer with $\delta > 4\big(d_0 \sum_j d_j\big)^2 n^3$. Then
--   $$\exists (y,s) \in P:\ f_1(y,s) \le 0 \quad\Longleftrightarrow\quad \exists (y,s) \in P:\ f_2(y,s) \le 0,$$
--   where $f_2(y,s) = f_1(y,s) + 2d_0 \sum_j d_j y_j (1 - y_j)$.
--
--   This step replaces the linear terms of $f_1$ in $y$ by quadratic ones ($y_j$ by $y_j^2$), the move toward a homogeneous quadratic form on $P$. It is where the size of $\delta$ enters.
--
--   **Formalization Note** Only the equivalence of the two existence questions is stated. The printed proof contains two false steps: the inequality "$(\delta/2)(y_j + s_j - 1)^2 + 2d_0 d_j y_j (1 - y_j) \ge 0$ for $y_j > 1$" fails for $y_j$ slightly above $1$, and the pointwise claim "for $(y,s) \in P$, $f_2(y,s) \le 0$ implies $f_1(y,s) \le 0$" is false (for $d = (3,5)$, $d_0 = 8$, $n = 2$, $\delta = 131073$, $y = (1 - 10^{-4}, 1 + 10^{-4})$, $s = 0$: $f_2 < 0 < f_1$). Neither is formalized.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 125, proof of Theorem 1, first paragraph (Problems 6 and 7 are equivalent)

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_Construction

namespace MurtyKabadi.Reduction

theorem problems6_7_equiv {n : ℕ} (d : Fin n → ℕ) (d0 δ : ℕ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ) :
    (∃ p ∈ P n, f1 d d0 δ p.1 p.2 ≤ 0) ↔ ∃ p ∈ P n, f2 d d0 δ p.1 p.2 ≤ 0 := by sorry

end MurtyKabadi.Reduction
