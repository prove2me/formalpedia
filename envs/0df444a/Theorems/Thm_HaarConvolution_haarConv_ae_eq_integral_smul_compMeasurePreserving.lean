-- Prove2me | Theorems.Thm_HaarConvolution_haarConv_ae_eq_integral_smul_compMeasurePreserving
-- name    : HaarConvolution.haarConv_ae_eq_integral_smul_compMeasurePreserving
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T20:11:29.16336+00:00
-- url     : https://prove2.me/theorems/17c17d56-207d-40ba-8677-477942a7eee8
-- title:
--   Left convolution $\psi*f$ with $\psi\in C_c(G)$, $f\in L^p(G)$, on a locally compact group equals a.e. the $L^p$-valued Bochner integral $\int\psi(y)\,\lambda_yf\,d\mu(y)$
-- statement:
--   **Left convolution with a compactly supported kernel is the $L^p$-valued integral of the left translates.** Let $G$ be a locally compact Hausdorff group with a left Haar measure $\mu$ (a Radon measure), let $1\le p<\infty$, let $f\in L^p(G,\mu)$ be complex-valued, and let $\psi\colon G\to\mathbb C$ be continuous with compact support. For $y\in G$ let $\lambda_yf\in L^p(G,\mu)$ denote the left translate
--
--   $$(\lambda_yf)(x)=f(y^{-1}x),\qquad x\in G .$$
--
--   By left invariance of $\mu$ each $\lambda_y$ is an isometry of $L^p(G,\mu)$, and $y\mapsto\lambda_yf$ is continuous, so $y\mapsto\psi(y)\,\lambda_yf$ is a continuous, compactly supported $L^p(G,\mu)$-valued function and has a Bochner integral $\int_G\psi(y)\,\lambda_yf\,d\mu(y)\in L^p(G,\mu)$. This integral is represented by the pointwise left convolution $\psi*f$:
--
--   $$(\psi*f)(x)=\int_G\psi(y)\,f(y^{-1}x)\,d\mu(y)=\Bigl(\int_G\psi(y)\,\lambda_yf\,d\mu(y)\Bigr)(x)\qquad\text{for $\mu$-almost every }x\in G .$$
--
--   This is the standard identification of a convolution with a continuous superposition of translates. Combined with the norm inequality for Bochner integrals, $\bigl\|\int_G\psi(y)\,\lambda_yf\,d\mu(y)\bigr\|_p\le\int_G|\psi(y)|\,\|\lambda_yf\|_p\,d\mu(y)$ (Minkowski's integral inequality), it gives the basic $L^p$ estimates for $\psi*f$, for instance $\|\psi*f\|_p\le\|\psi\|_1\|f\|_p$, and, for $\psi\ge0$ with $\int_G\psi\,d\mu=1$, the bound $\|\psi*f-f\|_p\le\sup_{y\in\operatorname{supp}\psi}\|\lambda_yf-f\|_p$ behind the convergence of approximate identities in $L^p(G)$ (the approximate units of §9.3 of the source). No second countability or $\sigma$-compactness of $G$ is assumed.
--
--   **Formalization Note.** The left Haar measure is `μ.IsHaarMeasure` (left-invariant) and its Radon property is `μ.Regular`. The translate $\lambda_yf$ is `Lp.compMeasurePreserving (fun x => y⁻¹ * x) (measurePreserving_mul_left μ y⁻¹) (hf.toLp f)`, the $L^p$ class of $x\mapsto f(y^{-1}x)$. The $L^p$-valued integral is Mathlib's Bochner integral in the Banach space `Lp ℂ p μ` (the instance `[Fact (1 ≤ p)]` records $p\ge1$), coerced to a function, i.e. any representative; its integrand is continuous with compact support (continuity of translation, Mathlib's `Continuous.compMeasurePreservingLp`), hence Bochner integrable, so Lean's junk value $0$ for non-integrable integrands does not occur on the right. The left-hand side is, for each $x$, the Bochner integral of $y\mapsto\psi(y)f(y^{-1}x)$ with respect to $\mu$ (classically this integral converges absolutely for every $x$). The case $p=\infty$ is excluded: translation is not continuous in $L^\infty$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 419, §9.3 (approximate units: nets of convolution operators converging to the identity in the topology of simple convergence), and pp. 422–424, Lemma 9.3.2.1 and its proof; auxiliary lemma for the proof of ApproxIdentity.eLpNorm_haarConv_sub_lt

import Mathlib

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

namespace HaarConvolution

theorem haarConv_ae_eq_integral_smul_compMeasurePreserving {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (ψ : G → ℂ) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (f : G → ℂ) (hf : MemLp f p μ) :
    (fun x : G => ∫ y, ψ y * f (y⁻¹ * x) ∂μ) =ᵐ[μ]
      ⇑(∫ y, ψ y • Lp.compMeasurePreserving (fun x : G => y⁻¹ * x)
        (measurePreserving_mul_left μ y⁻¹) (hf.toLp f) ∂μ) := by sorry

end HaarConvolution
