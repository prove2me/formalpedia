-- Prove2me | Theorems.Thm_GoldieRenewal_Kesten_inequalities_9_26_9_27
-- name    : GoldieRenewal.Kesten.inequalities_9_26_9_27
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:09:22.984367+00:00
-- url     : https://prove2.me/theorems/2faa9857-fa09-4abd-a720-51ece981451b
-- title:
--   (9.26)–(9.27) — |x + y|^r ≤ c_r(|x|^r + |y|^r) and the two-case bound on ||x|^r − |y|^r|
-- statement:
--   For all real $x,y$:
--
--   1. (9.26) for every $r>0$,
--   $$
--   |x+y|^r \le c_r\big(|x|^r+|y|^r\big),\qquad c_r := 2^{r-1}\vee 1 ;
--   $$
--   2. (9.27)
--   $$
--   \big||x|^r-|y|^r\big| \le \begin{cases} |x-y|^r, & 0<r\le 1,\\ r\,|x-y|\,(|x|\vee|y|)^{r-1}, & 1<r<\infty.\end{cases}
--   $$
--
--   These elementary inequalities control the moment differences $\mathbf E\big(((Q+MR)^+)^\kappa-((MR)^+)^\kappa\big)$ in the proof of Kesten's theorem.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 156, proof of Theorem 4.1, (9.26)–(9.27)

import Mathlib

namespace GoldieRenewal.Kesten

/-- **The elementary inequalities (9.26) and (9.27)** (Goldie, *Implicit renewal theory and tails
of solutions of random equations*, Ann. Appl. Probab. 1(1) (1991), p. 156, proof of Theorem 4.1).
For all real `x`, `y`:

* (9.26) for `r > 0`, `|x + y|^r ≤ c_r (|x|^r + |y|^r)` with `c_r := 2^{r−1} ∨ 1`;
* (9.27) `||x|^r − |y|^r| ≤ |x − y|^r` for `0 < r ≤ 1`, and
  `||x|^r − |y|^r| ≤ r |x − y| (|x| ∨ |y|)^{r−1}` for `1 < r < ∞`.

**Formalization Note** Powers are `Real.rpow` with nonnegative bases. -/
theorem inequalities_9_26_9_27 :
    (∀ x y r : ℝ, 0 < r → |x + y| ^ r ≤ max ((2 : ℝ) ^ (r - 1)) 1 * (|x| ^ r + |y| ^ r)) ∧
    (∀ x y r : ℝ, 0 < r → r ≤ 1 → abs (|x| ^ r - |y| ^ r) ≤ |x - y| ^ r) ∧
    (∀ x y r : ℝ, 1 < r → abs (|x| ^ r - |y| ^ r) ≤ r * |x - y| * (max |x| |y|) ^ (r - 1)) := by sorry

end GoldieRenewal.Kesten
