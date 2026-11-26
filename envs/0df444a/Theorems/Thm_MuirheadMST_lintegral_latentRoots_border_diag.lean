-- Prove2me | Theorems.Thm_MuirheadMST_lintegral_latentRoots_border_diag
-- name    : MuirheadMST.lintegral_latentRoots_border_diag
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T21:02:21.678131+00:00
-- url     : https://prove2.me/theorems/4af9f4b9-fa41-5c35-aaec-d21edcacea7f
-- title:
--   Latent roots of a bordered diagonal matrix: the secular change of variables
-- statement:
--   Let $\mu_1>\cdots>\mu_m$. For $b\in\mathbb R^m$ and $c\in\mathbb R$ let $l_1\ge\cdots\ge l_{m+1}$ be the latent roots of
--   $$\begin{pmatrix} c & b^{\mathsf T}\\ b & \operatorname{diag}(\mu)\end{pmatrix}.$$
--   Then the image of Lebesgue measure $db\,dc$ under $(b,c)\mapsto l$ has density
--   $$\prod_{1\le i<j\le m+1}(l_i-l_j)\ \prod_{i=1}^{m}\prod_{j=1}^{m+1}|\mu_i-l_j|^{-1/2}$$
--   on the interlacing region $l_1>\mu_1>l_2>\cdots>\mu_m>l_{m+1}$, and $0$ elsewhere: for every measurable $h\ge0$, $\int h(l)\,db\,dc$ equals the integral of $h$ against this density.
--
--   **Formalization Note** This is the Lebesgue-measure form of the cited density: there $c\sim N(0,1)$ and $b_j^2\sim\Gamma(\beta/2,1)$, and for $\beta=1$ (so $s_j=1/2$) dividing (2.27) by the Gaussian weight $(2\pi)^{-1/2}\pi^{-m/2}e^{-c^2/2-\|b\|^2}$ (using $\sum_j l_j^2=c^2+2\|b\|^2+\sum_i\mu_i^2$) leaves exactly the density above. Interlacing is written `∀ i, μ i < l i.castSucc ∧ l i.succ < μ i`; the bordered array is as in `MuirheadMST.lintegral_latentRoots_border`.
-- source:
--   P. J. Forrester and S. O. Warnaar, The importance of the Selberg integral, arXiv:0710.3981v1 (2007), https://arxiv.org/abs/0710.3981 (page numbers of the arXiv version), p. 15, eqs. (2.27), (2.28) and (2.30) with beta = 1, i.e. s_j = 1/2 (the eigenvalues of (2.30) are the zeros of (2.28) with mu_0 = c, a_i the diagonal entries and mu_i the squared border entries b_i^2); method of G. W. Anderson, A short proof of Selberg's generalized beta formula, Forum Math. 3 (1991), 415-417

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory

namespace MuirheadMST

theorem lintegral_latentRoots_border_diag (m : ℕ) (μ : Fin m → ℝ) (hμ : StrictAnti μ)
    (h : (Fin (m + 1) → ℝ) → ENNReal) (hh : Measurable h) :
    ∫⁻ p : (Fin m → ℝ) × ℝ, h (latentRoots
        ((Fin.cons (Fin.cons p.2 p.1 : Fin (m + 1) → ℝ)
          (fun i => (Fin.cons (p.1 i) (diagArray μ i) : Fin (m + 1) → ℝ)) :
            Fin (m + 1) → Fin (m + 1) → ℝ))) =
      ∫⁻ l : Fin (m + 1) → ℝ,
        (if ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i then
          ENNReal.ofReal (vandermondeProd l *
            ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2))
        else 0) * h l := by sorry

end MuirheadMST
