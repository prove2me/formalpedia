-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_proposition_5_9
-- name    : HScattered.Hyperplanes.proposition_5_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:36.50369+00:00
-- url     : https://prove2.me/theorems/f9683b49-12cc-497c-8003-6bd18e1b2056
-- title:
--   Proposition 5.9 — $b_s = q^{nr}(-1)^s(q^{-n};q)_s$
-- statement:
--   Let $q > 1$ be real, $n, r, s \in \mathbb N$ with $s \ge 1$ dividing $nr$, and $m = nr/s$. Let
--   $$b_s = \sum_{j=0}^{s}\sum_{k=0}^{s}\sum_{t=0}^{s} q^{\,rnj/s - rnt/s + (s-k)n(r-s)/s + \frac12(s-k-1)(s-k) + \frac12(t-1)t}\begin{bmatrix} s\\ k\end{bmatrix}_q\begin{bmatrix} k\\ j\end{bmatrix}_q\begin{bmatrix} j\\ t\end{bmatrix}_q (-1)^{t+k}.$$
--   Then
--   $$b_s = q^{nr}(-1)^s (q^{-n};q)_s .$$
--
--   With Proposition 5.8 this yields $a_s = b_s$ and hence $A = 0$.
--
--   **Formalization Note** As in Proposition 5.8: $m = rn/s$ with $s\,m = n\,r$, integer exponents, halves as binomial coefficients.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 24, Proposition 5.9 (b_s as defined on p. 23)

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_qPoch
import Definitions.Def_HScattered_Hyperplanes_abSums

namespace HScattered.Hyperplanes

/-- Proposition 5.9 (arXiv:1906.10590v2, p. 24): with `s ≥ 1` dividing `nr`,
`m = nr/s` (given by `s · m = n · r`) and real `q > 1`, the triple sum `b_s` of §5.4 (p. 23)
satisfies `b_s = q^{nr} (−1)^s (q^{−n}; q)_s`. -/
theorem proposition_5_9 (q : ℝ) (hq : 1 < q) (n r s m : ℕ) (hs : 0 < s) (hm : s * m = n * r) :
    bSum q n s m = q ^ (n * r) * (-1) ^ s * qPoch (q ^ (-(n : ℤ))) q s := by sorry

end HScattered.Hyperplanes
