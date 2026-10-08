-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_corollary_5_3
-- name    : HScattered.Hyperplanes.corollary_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:25:01.342011+00:00
-- url     : https://prove2.me/theorems/60d16e0e-e682-43aa-90b2-415d4f546134
-- title:
--   Corollary 5.3 — (21), (22) at $a = q^{-nr/s}$, $b = q^{nr/s-n}$
-- statement:
--   Let $q > 1$ be real, $n, r, s \in \mathbb N$ with $s \ge 1$ dividing $nr$, and $m = nr/s$. Then
--   $$(q^{-n};q)_s = \sum_{j=0}^{s} q^{j(nr/s - n)}\begin{bmatrix} s\\ j\end{bmatrix}_q (q^{-nr/s};q)_j\,(q^{nr/s-n};q)_{s-j}, \qquad (21)$$
--   $$(q^{-n};q)_s = q^{-nr}\sum_{j=0}^{s} q^{jnr/s}\begin{bmatrix} s\\ j\end{bmatrix}_q (q^{-nr/s};q)_j\,(q^{nr/s-n};q)_{s-j}. \qquad (22)$$
--
--   These are (19) and (20) at $a = q^{-nr/s}$, $b = q^{nr/s-n}$; they close the evaluations of $a_s$ and $b_s$ in Propositions 5.8 and 5.9.
--
--   **Formalization Note** $nr/s$ is the exact quotient, passed as $m$ with $s\,m = n\,r$ (never floor division); powers of $q$ with possibly negative exponents are integer powers.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 19, Corollary 5.3

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_HScattered_Hyperplanes_qPoch

namespace HScattered.Hyperplanes

/-- Corollary 5.3 (arXiv:1906.10590v2, p. 19): put `a = q^{−nr/s}` and `b = q^{nr/s−n}` in (19)
and (20). Here `s ≥ 1` divides `nr` and `m = nr/s` is given by `s · m = n · r`; powers of `q`
with possibly negative exponents are integer powers. For real `q > 1`:
(21) `(q^{−n}; q)_s = ∑_{j=0}^s q^{j(m−n)} [s j]_q (q^{−m}; q)_j (q^{m−n}; q)_{s−j}`,
(22) `(q^{−n}; q)_s = q^{−nr} ∑_{j=0}^s q^{j m} [s j]_q (q^{−m}; q)_j (q^{m−n}; q)_{s−j}`. -/
theorem corollary_5_3 (q : ℝ) (hq : 1 < q) (n r s m : ℕ) (hs : 0 < s) (hm : s * m = n * r) :
    qPoch (q ^ (-(n : ℤ))) q s = ∑ j ∈ Finset.range (s + 1),
        q ^ ((j : ℤ) * ((m : ℤ) - n)) * gaussBinom q s j *
          qPoch (q ^ (-(m : ℤ))) q j * qPoch (q ^ ((m : ℤ) - n)) q (s - j) ∧
      qPoch (q ^ (-(n : ℤ))) q s = q ^ (-((n : ℤ) * r)) * ∑ j ∈ Finset.range (s + 1),
        q ^ ((j : ℤ) * m) * gaussBinom q s j *
          qPoch (q ^ (-(m : ℤ))) q j * qPoch (q ^ ((m : ℤ) - n)) q (s - j) := by sorry

end HScattered.Hyperplanes
