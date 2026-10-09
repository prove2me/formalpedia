-- Prove2me | Theorems.Thm_GaussianMatrix_residual_law
-- name    : GaussianMatrix.residual_law
-- status  : Proved
-- author  : @tc
-- created : 2026-10-09T03:40:42.674018+00:00
-- url     : https://prove2.me/theorems/5a24538d-c196-47c7-a23a-023f49347438
-- title:
--   Residual of a standard Gaussian vector against a fixed $n$-dimensional row space is $\chi^2_{k-n}$
-- statement:
--   Let $H \in \mathbb{R}^{n \times k}$ be a fixed real matrix of full row rank, $\operatorname{rank} H = n$ (so $n \le k$ and $HH^\top$ is invertible), and let $g \sim \mathcal{N}(0, I_k)$ be a standard Gaussian vector in $\mathbb{R}^k$ (independent $\mathcal{N}(0,1)$ coordinates). Define the squared residual
--
--   $$Q_H(g) \;=\; g^\top g - (Hg)^\top (HH^\top)^{-1} (Hg) \;=\; \|(I - P_H)\,g\|_2^2, \qquad P_H = H^\top (HH^\top)^{-1} H,$$
--
--   the squared length of the component of $g$ orthogonal to the row space of $H$. Then $Q_H(g)$ has the chi-square distribution with $k-n$ degrees of freedom:
--
--   $$\operatorname{Law}\big(Q_H(g)\big) \;=\; \operatorname{Law}\Big(\textstyle\sum_{j=1}^{k-n} x_j^2\Big), \qquad x \sim \mathcal{N}(0, I_{k-n}).$$
--
--   This is the probabilistic step in the computation of $\mathbb{E}\,(GG^\top)^{-1}$: conditionally on the other rows of a Gaussian matrix, the residual of one row has a $\chi^2$ law whose degrees of freedom do not depend on those rows. It follows from rotation invariance of the standard Gaussian: if the columns of $V \in \mathbb{R}^{k \times (k-n)}$ form an orthonormal basis of $\ker H$, then $Q_H(g) = \|V^\top g\|^2$ and $V^\top g \sim \mathcal{N}(0, I_{k-n})$.
--
--   **Formalization Note.** Both laws are expressed as push-forward measures on $\mathbb{R}$ (`Measure.map`) of the product measures `Measure.pi fun _ => gaussianReal 0 1`; the subtraction $k - n$ is natural-number subtraction, which is exact because $\operatorname{rank} H = n$ forces $n \le k$.
-- source:
--   standard fact: if $g \sim N(0, I_k)$ and $P$ is an orthogonal projector on $\mathbb{R}^k$ of rank $k-n$, then $g^\top P g \sim \chi^2_{k-n}$ (rotation invariance of the standard Gaussian; cf. R. J. Muirhead, Aspects of Multivariate Statistical Theory, Wiley 1982, Ch. 1, and Halko–Martinsson–Tropp, SIAM Review 53(2) 2011, Appendix A).

import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem residual_law {n k : ℕ} (H : Matrix (Fin n) (Fin k) ℝ) (hH : H.rank = n) :
    Measure.map (fun g : Fin k → ℝ => g ⬝ᵥ g - (H *ᵥ g) ⬝ᵥ ((H * Hᵀ)⁻¹ *ᵥ (H *ᵥ g)))
        (Measure.pi fun _ : Fin k => gaussianReal 0 1)
      = Measure.map (fun x : Fin (k - n) → ℝ => ∑ j, x j ^ 2)
        (Measure.pi fun _ : Fin (k - n) => gaussianReal 0 1) := by sorry

end GaussianMatrix
