-- Prove2me | Theorems.Thm_GrothendieckConstant_coeff_hermite_moments
-- name    : GrothendieckConstant.coeff_hermite_moments
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-07T01:26:26.997192+00:00
-- url     : https://prove2.me/theorems/25dbc35b-7406-4bdc-9925-65d9e7a45944
-- title:
--   Hermite moment formulas for the coefficients $b_1$, $b_3$ of a Krivine scheme
-- statement:
--   Let $S=(f,g)$ be a Krivine scheme of dimension $k$, let $X$ be a standard Gaussian vector in $\mathbb R^k$ with density $\varphi(x)=\prod_{m}(2\pi)^{-1/2}e^{-x_m^2/2}$, and let $H(t)=b_1t+b_3t^3+\cdots$ be the normalized correlation function of the scheme, with $b_1=H'(0)$ (`coeffLinear`) and $b_3=H'''(0)/6$ (`coeffCubic`).
--
--   For a function $h$ on $\mathbb R^k$ write $a_h=\mathbb E[h(X)X]\in\mathbb R^k$ for its first-order Hermite moments and $T_h=\mathbb E[h(X)\,\mathbf H_3(X)]$ for its third-order Hermite moments, where
--   $$\mathbf H_3(x)_{ijl}=x_ix_jx_l-\delta_{ij}x_l-\delta_{il}x_j-\delta_{jl}x_i$$
--   is the third Hermite tensor. Then
--   $$b_1=\frac{\pi}{2}\,\langle a_f,a_g\rangle=\frac{\pi}{2}\sum_i a_{f,i}\,a_{g,i},\qquad b_3=\frac{\pi}{12}\,\langle T_f,T_g\rangle=\frac{\pi}{12}\sum_{i,j,l}T_{f,ijl}\,T_{g,ijl}.$$
--
--   This is the order-one and order-three part of the Hermite (Mehler) expansion of the correlation function. It makes precise the paper's remark that $(b_1,b_3)$ are linear functionals of each of $f$ and $g$, so that affine constraints in $(b_1,b_3)$ pass to mixtures and limits of schemes.
--
--   **Proof outline.** The Gaussian pair density equals $c(t)^k\exp\big(-(A-2tB)/(2(1-t^2))\big)$ with $A=|x|^2+|y|^2$ and $B=\langle x,y\rangle$. Its first three $t$-derivatives are bounded on $|t|\le 1/2$ by $500(1+A+k)^3e^{-A/4}$, which is integrable, so the correlation function can be differentiated three times under the integral sign. At $t=0$ the third derivative of the density is the density times $B^3-3AB+(3k+6)B=\sum_{i,j,l}\mathbf H_3(x)_{ijl}\mathbf H_3(y)_{ijl}$, and the double integrals factor by Fubini.
-- source:
--   Li, Saha, Xue, Chaudhuri, Klivans, Kothari, Meka, "Long-Horizon AI Research for Grothendieck Constant: A Case Study in Human-AI Mathematical Collaboration", arXiv:2608.11195v3 (2026), https://arxiv.org/abs/2608.11195, Section 2, p. 6 (definition of the coefficients b1, b3 of H) and Appendix A, p. 17 (the Hermite coefficients (b1, b3) are linear functionals of the scheme). Standard Mehler/Hermite expansion of the bivariate Gaussian density.

import Mathlib
import Definitions.Def_KrivineSchemeDefs

open MeasureTheory ProbabilityTheory Real

namespace GrothendieckConstant

theorem coeff_hermite_moments (k : ℕ) (S : KrivineScheme k) :
    coeffLinear S = (π / 2) * ∑ i : Fin k,
        (∫ x, S.f x * x i * ∏ m, gaussianPDFReal 0 1 (x m)) *
        (∫ y, S.g y * y i * ∏ m, gaussianPDFReal 0 1 (y m)) ∧
    coeffCubic S = (π / 12) * ∑ i : Fin k, ∑ j : Fin k, ∑ l : Fin k,
        (∫ x, S.f x * (x i * x j * x l - (if i = j then x l else 0) - (if i = l then x j else 0)
            - (if j = l then x i else 0)) * ∏ m, gaussianPDFReal 0 1 (x m)) *
        (∫ y, S.g y * (y i * y j * y l - (if i = j then y l else 0) - (if i = l then y j else 0)
            - (if j = l then y i else 0)) * ∏ m, gaussianPDFReal 0 1 (y m)) := by sorry

end GrothendieckConstant
