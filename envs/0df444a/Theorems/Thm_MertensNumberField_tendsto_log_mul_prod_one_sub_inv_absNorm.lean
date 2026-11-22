-- Prove2me | Theorems.Thm_MertensNumberField_tendsto_log_mul_prod_one_sub_inv_absNorm
-- name    : MertensNumberField.tendsto_log_mul_prod_one_sub_inv_absNorm
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:35.487448+00:00
-- url     : https://prove2.me/theorems/7cf44cf0-43e4-423c-9dad-5c2240f378c8
-- title:
--   Mertens' theorem for number fields — $\prod_{N(\mathfrak p)<x}\bigl(1-N(\mathfrak p)^{-1}\bigr)\sim e^{-\gamma}/(\kappa_F\log x)$ with $\kappa_F=\operatorname{Res}_{s=1}\zeta_F$
-- statement:
--   **Mertens' theorem for number fields.** Let $F$ be a number field with ring of integers $\mathcal O_F$, let $N(\mathfrak p)$ denote the absolute norm of a nonzero prime ideal $\mathfrak p\subset\mathcal O_F$, let $\gamma$ be the Euler–Mascheroni constant, and let
--   $$\kappa_F=\operatorname{Res}_{s=1}\zeta_F(s)=\frac{2^{r_1}(2\pi)^{r_2}h_FR_F}{w_F\,|d_F|^{1/2}}$$
--   be the residue at $s=1$ of the Dedekind zeta function of $F$ ($r_1$, $r_2$ the numbers of real and complex places, $h_F$ the class number, $R_F$ the regulator, $w_F$ the number of roots of unity, $d_F$ the discriminant). Then, as $x\to+\infty$,
--   $$\prod_{\mathfrak p\subset\mathcal O_F,\ N(\mathfrak p)<x}\Bigl(1-\frac1{N(\mathfrak p)}\Bigr)=\frac{e^{-\gamma}}{\kappa_F\,\log x}\,\bigl(1+o(1)\bigr),$$
--   that is,
--   $$\lim_{x\to+\infty}\ \log x\prod_{N(\mathfrak p)<x}\Bigl(1-\frac1{N(\mathfrak p)}\Bigr)=\frac{e^{-\gamma}}{\kappa_F}.$$
--
--   This is equation (B.7.2.25) of Remark B.7.2.6 of the source ("Mertens' Theorem for the number field $F$"), where the constant is written $\overline\mu_1(C_F^1)$, the volume of the norm-one idele class group $C_F^1$ for the source's Tamagawa measure, which by its eq. (A.3.2.1) is the number $\kappa_F$ above. For $F=\mathbb Q$ one has $\kappa_{\mathbb Q}=1$ and the statement is Mertens' third theorem $\prod_{p<x}(1-1/p)\sim e^{-\gamma}/\log x$. It describes the reciprocal partial Euler products $E_{f,x}(s,\chi)$ of $L_f(s,\chi)=\zeta_F(s-it_0)$ at the pole $s=1+it_0$, the one point of the line $\operatorname{Re}(s)=1$ where they do not converge to $1/L_f$ locally uniformly (Remark B.7.2.7).
--
--   **Formalization Note.** The statement uses Mathlib only. The product over the prime ideals with $N(\mathfrak p)<x$ is a `finprod` over the finite places `v : HeightOneSpectrum (𝓞 F)` with `(Ideal.absNorm v.asIdeal : ℝ) < x` (a finite set); $\gamma$ is `Real.eulerMascheroniConstant` and $\kappa_F$ is Mathlib's `NumberField.dedekindZeta_residue F`, defined by the displayed class-number-formula expression and proved in Mathlib to be the residue of `NumberField.dedekindZeta F` at $1$ (`NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`). The asymptotic equality with factor $1+o_x(1)$ is expressed as the convergence of $\log x$ times the product.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 653, Remark B.7.2.6, eq. (B.7.2.25); classical reference: G. H. Hardy and E. M. Wright, An Introduction to the Theory of Numbers, Fourth Edition, Oxford, 1960, Theorem 429 (p. 351) (the case F = Q, whose argument the source follows); S. R. Garcia and E. S. Lee, Unconditional explicit Mertens' theorems for number fields and Dedekind zeta residue bounds, The Ramanujan Journal 57 (2022), 1169–1191, Theorem 1, (C1)

import Mathlib

open Filter Topology NumberField IsDedekindDomain

set_option autoImplicit false

namespace MertensNumberField

theorem tendsto_log_mul_prod_one_sub_inv_absNorm (F : Type*) [Field F] [NumberField F] :
    Tendsto
      (fun x : ℝ => Real.log x *
        ∏ᶠ (v : HeightOneSpectrum (𝓞 F)) (_ : (Ideal.absNorm v.asIdeal : ℝ) < x),
          (1 - ((Ideal.absNorm v.asIdeal : ℝ))⁻¹))
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant) / dedekindZeta_residue F)) := by sorry

end MertensNumberField
