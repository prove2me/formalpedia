-- Prove2me | Theorems.Thm_GaussianMatrix_sMin_lower_tail
-- name    : GaussianMatrix.sMin_lower_tail
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T02:47:53.286117+00:00
-- url     : https://prove2.me/theorems/887f572a-fd4f-4024-a53c-2bc35276fabf
-- title:
--   One-sided Gaussian tail for the smallest singular value: $\mathbb P\{s_{\min}(A)\le\sqrt N-\sqrt n-u\}\le e^{-u^2/2}$
-- statement:
--   Let $A\in\mathbb R^{N\times n}$ be a standard Gaussian matrix with $1\le n\le N$ and let $s_{\min}(A)=\inf_{\|x\|_2=1}\|Ax\|_2$ be its smallest singular value. For every $u\ge0$,
--   $$\mathbb P\bigl\{s_{\min}(A)\le\sqrt N-\sqrt n-u\bigr\}\ \le\ e^{-u^2/2}.$$
--
--   This is the one-sided form of the deviation inequality for $s_{\min}$: Gordon's inequality gives $\mathbb E\,s_{\min}(A)\ge\sqrt N-\sqrt n$, and one-sided Gaussian concentration for the $1$-Lipschitz function $A\mapsto s_{\min}(A)$ gives $\mathbb P\{s_{\min}\le\mathbb E s_{\min}-u\}\le e^{-u^2/2}$. It saves the factor $2$ of the two-sided corollary, and it is the tail bound used to control inverse moments of $\sigma_{\min}$ of a Gaussian sketch in the regime $s$ close to $\sqrt N-\sqrt n$.
--
--   **Formalization Note.** For a wide $k\times t$ Gaussian matrix $G$ ($k\le t$) the usual $\sigma_{\min}(G)$ equals $s_{\min}(G^{\mathsf T})$, so the wide form is this statement with $(N,n)=(t,k)$. The event uses $\le$; Davidson–Szarek state it with $<$ for the matrix normalized by $N^{-1/2}$.
-- source:
--   K. R. Davidson, S. J. Szarek, *Local operator theory, random matrices and Banach spaces*, Handbook of the Geometry of Banach Spaces, Vol. 1, 317–366, 2001, https://doi.org/10.1016/S1874-5849(01)80010-3, §II.7 p. 334, Theorem II.13: for an $N\times n$ matrix $\Gamma$ with independent $\mathcal N(0,1/N)$ entries and $t>0$, $\mathbb P\{s_{\min}(\Gamma)<1-\sqrt{n/N}-t\}\le e^{-Nt^2/2}$ (rescaling by $\sqrt N$ gives the statement with $\le$ by right-continuity of the bound). Equivalently the one-sided form of R. Vershynin, *Introduction to the non-asymptotic analysis of random matrices*, Chapter 5 of Compressed Sensing: Theory and Applications (Y. Eldar, G. Kutyniok, eds.), Cambridge University Press, 2012, https://arxiv.org/abs/1011.3027 (v7), §5.3.1 p. 21, Corollary 5.35, obtained from Theorem 5.32 ($\mathbb E s_{\min}\ge\sqrt N-\sqrt n$) and Proposition 5.34 applied to the $1$-Lipschitz function $-s_{\min}$.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix
theorem sMin_lower_tail {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (u : ℝ) (hu : 0 ≤ u) :
    (gaussianMatrix N n) {A | sMin (Matrix.of A) ≤ Real.sqrt N - Real.sqrt n - u}
      ≤ ENNReal.ofReal (Real.exp (-u ^ 2 / 2)) := by sorry
end GaussianMatrix
