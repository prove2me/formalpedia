-- Prove2me | Theorems.Thm_MuirheadMST_dixonAnderson_half
-- name    : MuirheadMST.dixonAnderson_half
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T21:02:22.4457+00:00
-- url     : https://prove2.me/theorems/55d7eb7c-9dd7-5caa-9140-80def0f65ad4
-- title:
--   The Dixon–Anderson integral with all exponents equal to 1/2
-- statement:
--   Let $l_1>l_2>\cdots>l_{m+1}$. Then
--   $$\int_{l_1>\mu_1>l_2>\cdots>\mu_m>l_{m+1}} \prod_{1\le i<j\le m}(\mu_i-\mu_j)\prod_{i=1}^{m}\prod_{j=1}^{m+1}|\mu_i-l_j|^{-1/2}\,d\mu_1\cdots d\mu_m=\frac{\pi^{(m+1)/2}}{\Gamma\big(\frac{m+1}{2}\big)}.$$
--   This is the Dixon–Anderson integral with $s_1=\cdots=s_{m+1}=1/2$: the right side of the cited formula is $\Gamma(1/2)^{m+1}/\Gamma((m+1)/2)$ times $\prod_{i<j}(l_i-l_j)^{s_i+s_j-1}=1$.
--
--   **Formalization Note** The cited survey states the formula under $\operatorname{Re}(s_i)>1$; both sides are analytic in each $s_i$ on $\operatorname{Re}(s_i)>0$, where the integral converges absolutely, so it holds there, in particular at $s_i=1/2$. The integral is an `ENNReal` lintegral over $\mathbb R^m$ of the integrand times the indicator of the interlacing region; for $m=0$ both sides are $1$.
-- source:
--   P. J. Forrester and S. O. Warnaar, The importance of the Selberg integral, arXiv:0710.3981v1 (2007), https://arxiv.org/abs/0710.3981 (page numbers of the arXiv version), p. 13, eq. (2.24) (Dixon-Anderson integral), with n = m and s_j = 1/2; A. L. Dixon, Generalizations of Legendre's formula, Proc. London Math. Soc. 3 (1905), 206-224, and G. W. Anderson, Forum Math. 3 (1991), 415-417

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory

namespace MuirheadMST

theorem dixonAnderson_half (m : ℕ) (l : Fin (m + 1) → ℝ) (hl : StrictAnti l) :
    ∫⁻ μ : Fin m → ℝ,
        (if ∀ i : Fin m, μ i < l i.castSucc ∧ l i.succ < μ i then
          ENNReal.ofReal (vandermondeProd μ *
            ∏ i : Fin m, ∏ j : Fin (m + 1), |μ i - l j| ^ (-(1 : ℝ) / 2))
        else 0) =
      ENNReal.ofReal (Real.pi ^ (((m : ℝ) + 1) / 2) / Real.Gamma (((m : ℝ) + 1) / 2)) := by sorry

end MuirheadMST
