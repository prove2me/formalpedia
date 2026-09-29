-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_problems7_8_equiv
-- name    : MurtyKabadi.Reduction.problems7_8_equiv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:15:15.354017+00:00
-- url     : https://prove2.me/theorems/657d23b2-fc2e-49a5-8aac-1ff4630fa958
-- title:
--   Proof of Theorem 1, p. 125 — Problems 7 and 8 are equivalent
-- statement:
--   Let $n \ge 1$, let $d_0; d_1, \dots, d_n$ be positive integers and $\delta$ an integer with $\delta > 4\big(d_0 \sum_j d_j\big)^2 n^3$. Then
--   $$\exists (y,s) \in P:\ f_2(y,s) \le 0 \quad\Longleftrightarrow\quad \exists (y,s) \in P:\ f_4(y,s) \le 0.$$
--
--   On $P$ the constant and linear terms of $f_2$ are rewritten using $\sum_j (y_j + s_j) = n$, which turns $f_2$ into the quadratic form $f_4$; this makes the problem a question about a homogeneous quadratic on the simplex-like set $P$.
--
--   **Formalization Note** The hypothesis $n \ge 1$ is the paper's tacit assumption. At $n = 0$ the statement is false in Lean: $P = \{(0,0)\}$, $f_2 = d_0^2 > 0$ there, while $f_4 = 0$ because every sum is empty and $a/0 = 0$.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 125, proof of Theorem 1, second paragraph (Problems 7 and 8 are equivalent)

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_Construction

namespace MurtyKabadi.Reduction

theorem problems7_8_equiv {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (d0 δ : ℕ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ) :
    (∃ p ∈ P n, f2 d d0 δ p.1 p.2 ≤ 0) ↔ ∃ p ∈ P n, f4 d d0 δ p.1 p.2 ≤ 0 := by sorry

end MurtyKabadi.Reduction
