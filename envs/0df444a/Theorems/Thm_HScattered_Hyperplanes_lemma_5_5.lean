-- Prove2me | Theorems.Thm_HScattered_Hyperplanes_lemma_5_5
-- name    : HScattered.Hyperplanes.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:42.605983+00:00
-- url     : https://prove2.me/theorems/2c64ad12-7ccd-405f-9851-ee3eb4df4635
-- title:
--   Lemma 5.5 — $\sigma_{k,l} = q^{l(l-1)/2}[k+1\ l]_q$
-- statement:
--   Let $q > 1$ be real and let $\sigma_{k,l}$ be the $l$-th elementary symmetric polynomial in $k+1$ variables evaluated at $1, q, q^2, \dots, q^k$. Then for all $k, l \in \mathbb N$,
--   $$\sigma_{k,l} = q^{l(l-1)/2}\begin{bmatrix} k+1\\ l\end{bmatrix}_q .$$
--
--   This is a classical identity ([6, Proposition 6.7 (b)] in the paper's references); §5.3 uses it to rewrite the expansion coefficients of $\prod_j (x - q^j)$ as Gaussian binomials.
--
--   **Formalization Note** $l(l-1)/2$ is the binomial coefficient $\binom{l}{2}$. The identity is stated for all real $q > 1$, which includes every prime power; both sides vanish for $l > k+1$.
-- source:
--   B. Csajbók, G. Marino, O. Polverino, F. Zullo, Generalising the scattered property of subspaces, arXiv:1906.10590v2, p. 19, Lemma 5.5 (citing [6, Proposition 6.7 (b)])

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_HScattered_Hyperplanes_sigma

namespace HScattered.Hyperplanes

/-- Lemma 5.5 (arXiv:1906.10590v2, p. 19; [6, Proposition 6.7 (b)]): for real `q > 1`,
`σ_{k,l} = q^{l(l−1)/2} [k+1  l]_q`, with `l(l−1)/2 = C(l, 2)`. -/
theorem lemma_5_5 (q : ℝ) (hq : 1 < q) (k l : ℕ) :
    sigma q k l = q ^ (l.choose 2) * gaussBinom q (k + 1) l := by sorry

end HScattered.Hyperplanes
