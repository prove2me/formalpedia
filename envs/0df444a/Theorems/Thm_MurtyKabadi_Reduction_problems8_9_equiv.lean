-- Prove2me | Theorems.Thm_MurtyKabadi_Reduction_problems8_9_equiv
-- name    : MurtyKabadi.Reduction.problems8_9_equiv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:16:32.178732+00:00
-- url     : https://prove2.me/theorems/f3de5268-1e12-437c-8252-c04e94be65f5
-- title:
--   Proof of Theorem 1, p. 125 — Problems 8 and 9 are equivalent
-- statement:
--   Let $n \ge 1$ and let $d_0; d_1, \dots, d_n$ be positive integers. Let $l$ be the total number of decimal digits of $d_0, d_1, \dots, d_n$, let $\delta$ be an integer with $\delta > 4\big(d_0 \sum_j d_j\big)^2 n^3$, and let $\varepsilon$ be a rational number with
--   $$0 < \varepsilon < 2^{-n l^2}.$$
--   Then
--   $$\exists (y,s) \in P:\ f_4(y,s) \le 0 \quad\Longleftrightarrow\quad \exists (y,s) \in P:\ f_5(y,s) < 0.$$
--
--   Since $f_5 = f_4 - \varepsilon$ on $P$, this says that when $f_4$ is positive on all of $P$, its minimum over $P$ is at least $\varepsilon$: the explicit, polynomially-sized precision is enough to turn the non-strict question into a strict one.
--
--   **Formalization Note** The bound $\varepsilon < 2^{-nl^2}$ is written multiplicatively, $\varepsilon \cdot 2^{n l^2} < 1$, in $\mathbb Q$. The hypothesis $n \ge 1$ is the paper's tacit assumption; at $n = 0$ both $f_4$ and $f_5$ vanish on $P = \{(0,0)\}$ in Lean, and the statement would be false.
-- source:
--   Murty and Kabadi, Some NP-complete problems in quadratic and nonlinear programming, Math. Programming 39 (1987), p. 125, proof of Theorem 1, second paragraph (Problems 8 and 9 are equivalent); ε and l defined on p. 123

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_SubsetSum
import Definitions.Def_MurtyKabadi_Reduction_Construction

namespace MurtyKabadi.Reduction

theorem problems8_9_equiv {n : ℕ} (hn : 0 < n) (d : Fin n → ℕ) (d0 δ : ℕ) (ε : ℚ)
    (hd : ∀ j, 0 < d j) (hd0 : 0 < d0)
    (hδ : 4 * (d0 * ∑ j, d j) ^ 2 * n ^ 3 < δ)
    (hε0 : 0 < ε) (hε : ε * (2 : ℚ) ^ (n * digitCount d d0 ^ 2) < 1) :
    (∃ p ∈ P n, f4 d d0 δ p.1 p.2 ≤ 0) ↔ ∃ p ∈ P n, f5 d d0 δ ε p.1 p.2 < 0 := by sorry

end MurtyKabadi.Reduction
