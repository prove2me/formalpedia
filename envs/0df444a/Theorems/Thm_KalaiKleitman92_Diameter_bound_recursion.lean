-- Prove2me | Theorems.Thm_KalaiKleitman92_Diameter_bound_recursion
-- name    : KalaiKleitman92.Diameter.bound_recursion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T04:04:09.023424+00:00
-- url     : https://prove2.me/theorems/3f167250-f643-41c3-93ad-291786a5f1cc
-- title:
--   p. 2, proof of Theorem 1 — "which implies the statement of the theorem": ⌊n^(log₂ d + 2)⌋ is a supersolution of the recursion
-- statement:
--   For natural numbers $d,n$ write $N(d,n)=\lfloor n^{\log_2 d+2}\rfloor$. If $d\ge2$ and $n\ge d+1$, then
--
--   $$N(d-1,\,n-1)+2\,N\!\left(d,\lfloor n/2\rfloor\right)+2\;\le\;N(d,n).$$
--
--   This is the arithmetic content of "which implies the statement of the theorem" in Kalai and Kleitman's proof: the bound $n^{\log d+2}$ of Theorem 1 satisfies the recursion $\Delta(d,n)\le\Delta(d-1,n-1)+2\Delta(d,[n/2])+2$, so an induction on $d+n$ carries the bound from smaller cases to $(d,n)$.
--
--   **Formalization Note** The paper does not print the base of the logarithm; base $2$ is the one the halving step produces. The power is the real power $n^{\log_2 d+2}$ and $N$ is its floor; since a distance is a natural number, $\operatorname{dist}\le n^{\log_2 d+2}$ is the same as $\operatorname{dist}\le N(d,n)$. $[n/2]$ is $\lfloor n/2\rfloor$. Under $d\ge2$, $n\ge d+1$ the natural-number differences $d-1$ and $n-1$ are the true ones.
-- source:
--   Kalai and Kleitman, A quasi-polynomial bound for the diameter of graphs of polyhedra, Bull. Amer. Math. Soc. 26 (1992), 315–316 (text of arXiv:math/9204233v1), p. 2, proof of Theorem 1 ("… which implies the statement of the theorem")

import Mathlib
import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace KalaiKleitman92.Diameter

/-- Kalai–Kleitman (1992), p. 2, proof of Theorem 1: "which implies the statement of the
theorem". The bound `N(d, n) = ⌊n ^ (log₂ d + 2)⌋` satisfies the recursion
`N(d − 1, n − 1) + 2 N(d, ⌊n/2⌋) + 2 ≤ N(d, n)` whenever `2 ≤ d` and `d + 1 ≤ n`. -/
theorem bound_recursion (d n : ℕ) (hd : 2 ≤ d) (hn : d + 1 ≤ n) :
    ⌊((n - 1 : ℕ) : ℝ) ^ (Real.logb 2 ((d - 1 : ℕ) : ℝ) + 2)⌋₊
      + 2 * ⌊((n / 2 : ℕ) : ℝ) ^ (Real.logb 2 (d : ℝ) + 2)⌋₊ + 2
      ≤ ⌊(n : ℝ) ^ (Real.logb 2 (d : ℝ) + 2)⌋₊ := by sorry

end KalaiKleitman92.Diameter
