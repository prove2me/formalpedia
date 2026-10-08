-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_proposition_5_8
-- name    : HScattered.Hyperplanes.proposition_5_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:49.322882+00:00
-- url     : https://prove2.me/theorems/c79f61eb-bca3-4994-b691-b9ac752ad391
-- title:
--   Proposition 5.8 — $a_s = q^{nr}(-1)^s(q^{-n};q)_s$
-- statement:
--   Let $q > 1$ be real, $n, r, s \in \mathbb N$ with $s \ge 1$ dividing $nr$, and $m = nr/s$. Let
--   $$a_s = \sum_{j=0}^{s} q^{nr-nj}\sum_{k=0}^{s}\sum_{t=0}^{s} q^{\,rnj/s - rnt/s + (s-k)n(r-s)/s + \frac12(s-k-1)(s-k) + \frac12(t-1)t}\begin{bmatrix} s\\ k\end{bmatrix}_q\begin{bmatrix} k\\ j\end{bmatrix}_q\begin{bmatrix} j\\ t\end{bmatrix}_q (-1)^{t+k}.$$
--   Then
--   $$a_s = q^{nr}(-1)^s (q^{-n};q)_s .$$
--
--   Together with Proposition 5.9 this gives $a_s = b_s$, which is equivalent to $A = 0$.
--
--   **Formalization Note** $rn/s$ is passed as $m$ with $s\,m = n\,r$; $n(r-s)/s = m - n$; the halves are $\binom{s-k}{2}$ and $\binom{t}{2}$; exponents are integers.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 23, Proposition 5.8 (a_s as defined on p. 23)

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_qPoch
import Definitions.Def_HScattered_Hyperplanes_abSums

namespace HScattered.Hyperplanes

/-- Proposition 5.8 (arXiv:1906.10590v2, p. 23): with `s ≥ 1` dividing `nr`,
`m = nr/s` (given by `s · m = n · r`) and real `q > 1`, the triple sum `a_s` of §5.4 (p. 23)
satisfies `a_s = q^{nr} (−1)^s (q^{−n}; q)_s`. -/
theorem proposition_5_8 (q : ℝ) (hq : 1 < q) (n r s m : ℕ) (hs : 0 < s) (hm : s * m = n * r) :
    aSum q n r s m = q ^ (n * r) * (-1) ^ s * qPoch (q ^ (-(n : ℤ))) q s := by sorry

end HScattered.Hyperplanes
