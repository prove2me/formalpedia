-- Prove2me | Theorems.Thm_GaussianMatrix_inverse_wishart_diag_law
-- name    : GaussianMatrix.inverse_wishart_diag_law
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T04:57:15.559989+00:00
-- url     : https://prove2.me/theorems/d40d3093-de05-4700-ac67-22d732d697f8
-- title:
--   Each diagonal entry of an inverse Wishart matrix is a reciprocal chi-square: $((GG^\top)^{-1})_{ii} \sim 1/\chi^2_{k-r+1}$
-- statement:
--   Let $1 \le r \le k$ and let $G \in \mathbb{R}^{r\times k}$ be a standard Gaussian matrix, i.e. its $rk$ entries are independent $\mathcal{N}(0,1)$ random variables. Let $W = GG^\top \in \mathbb{R}^{r\times r}$ be the associated Wishart matrix and fix a row index $i \in \{1,\dots,r\}$. Then the $i$-th diagonal entry of $W^{-1}$ has the law of the reciprocal of a chi-square variable with $k-r+1$ degrees of freedom:
--
--   $$\big(W^{-1}\big)_{ii} \;\overset{d}{=}\; \frac{1}{\Xi}, \qquad \Xi = \sum_{j=1}^{k-r+1} x_j^2,\quad x \sim \mathcal{N}(0, I_{k-r+1}).$$
--
--   Equivalently, $1/(W^{-1})_{ii} = \|(I-P_{-i})g_i\|_2^2 \sim \chi^2_{k-r+1}$, where $g_i$ is the $i$-th row of $G$ and $P_{-i}$ is the orthogonal projector onto the span of the other $r-1$ rows. The proof combines the Schur-complement formula for a diagonal entry of an inverse, the fact that the other $r-1$ rows are almost surely linearly independent, and the rotation invariance of the Gaussian row $g_i$, which is independent of the other rows (Fubini over rows).
--
--   This identifies the law of each summand in $\|G^\dagger\|_F^2 = \operatorname{tr}(W^{-1}) = \sum_i (W^{-1})_{ii}$; together with $L^q$ bounds for reciprocal chi-square variables it yields tail bounds for the Frobenius norm of a pseudo-inverted Gaussian matrix.
--
--   **Formalization Note.** Laws are push-forward measures on $\mathbb{R}$ (`Measure.map`). Lean's matrix inverse is total ($A^{-1}=0$ for singular $A$) and $0^{-1}=0$, so both maps are defined everywhere; the singular events are null. The hypothesis $r \le k$ is needed: for $r = k+1$ the natural-number expression $k-r+1$ would equal $1$, whereas $W$ is then singular.
-- source:
--   standard fact: if $A \sim W_r(k, I)$ with $k \ge r$, then $1/(A^{-1})_{ii} \sim \chi^2_{k-r+1}$; see R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley 1982, Theorem 3.2.11 (with $M = e_i^\top$); it is also the computation underlying N. Halko, P.-G. Martinsson, J. A. Tropp, Finding structure with randomness: Probabilistic algorithms for constructing approximate matrix decompositions, SIAM Review 53(2) (2011), 217–288 (arXiv:0909.4061), Proposition A.5.

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem inverse_wishart_diag_law {r k : ℕ} (hrk : r ≤ k) (i : Fin r) :
    Measure.map (fun G : Fin r → Fin k → ℝ => (Matrix.of G * (Matrix.of G)ᵀ)⁻¹ i i)
        (gaussianMatrix r k)
      = Measure.map (fun x : Fin (k - r + 1) → ℝ => (∑ j, x j ^ 2)⁻¹)
        (Measure.pi fun _ : Fin (k - r + 1) => gaussianReal 0 1) := by sorry

end GaussianMatrix
