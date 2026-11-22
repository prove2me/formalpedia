-- Prove2me | Theorems.Thm_HardyHalfPlane_cauchy_integral_formula
-- name    : HardyHalfPlane.cauchy_integral_formula
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T15:24:39.374282+00:00
-- url     : https://prove2.me/theorems/85dad0d3-fbc3-49d1-851e-2d09be545a33
-- title:
--   Cauchy integral formula for the Hardy space $H^p(\mathbf C_{<a})$ of a half-plane, $1\le p<\infty$
-- statement:
--   **Cauchy integral formula for Hardy functions on a half-plane.** Let $a\in\mathbb R$, let $1\le p<\infty$, and let $\Phi\in H^p(\mathbf C_{<a})$: $\Phi$ is holomorphic on $\mathbf C_{<a}=\{\operatorname{Re}(s)<a\}$ and $\sup_{\sigma<a}\|\Phi(\sigma+i\,\cdot\,)\|_{L^p(\mathbb R)}<\infty$. Let $a'\le a$ and let $g$ be the function $\Phi$ on the vertical line $\operatorname{Re}(s)=a'$, that is
--
--   $$g(y)=\lim_{\sigma\to a'^-}\Phi(\sigma+iy)\qquad\text{for almost every }y\in\mathbb R$$
--
--   (for $a'<a$ this is simply $g(y)=\Phi(a'+iy)$; for $a'=a$ it is the boundary function of $\Phi$). Then for every $z\in\mathbb C$ with $\operatorname{Re}(z)\ne a'$ the integral below converges absolutely and
--
--   $$\frac1{2\pi i}\int_{a'-i\infty}^{a'+i\infty}\frac{\Phi(s)}{s-z}\,\mathrm ds\;=\;\frac1{2\pi}\int_{\mathbb R}\frac{g(y)}{a'+iy-z}\,\mathrm dy\;=\;\begin{cases}\Phi(z),&\operatorname{Re}(z)<a',\\[2pt] 0,&\operatorname{Re}(z)>a'.\end{cases}$$
--
--   So a function of $H^p(\mathbf C_{<a})$, $p\ge1$, is reproduced inside the half-plane by the Cauchy integral of its values on a single vertical line, and that Cauchy integral vanishes on the other side of the line. The source recalls this formula in §B.2.1 as the prototype of its "asymptotic Cauchy integral formula", in which the Hardy condition is replaced by rapid decay on vertical strips and two lines of integration are needed.
--
--   **Formalization Note.** The upward vertical line integral is written in the parameter $s=a'+iy$, $\mathrm ds=i\,\mathrm dy$, which turns $\frac1{2\pi i}\int\cdot\,\mathrm ds$ into $\frac1{2\pi}\int_{\mathbb R}\cdot\,\mathrm dy$. The function $g$ is any function that is almost everywhere the limit of $\Phi(\sigma+iy)$ as $\sigma\to a'^-$ (filter `𝓝[<] a'`). Integrability of the integrand is part of the conclusion, because Mathlib's Bochner integral of a non-integrable function is $0$ by convention. The case distinction is an `if … then … else`, used only for $\operatorname{Re}(z)\ne a'$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 592, §B.2.1 (the two displayed Cauchy formulas for $\Phi\in H^p(\mathbf C_{<a})$, $p\ge1$, on the lines $\operatorname{Re}(s)=a'\le a$); classical reference: P. Duren, Theory of $H^p$ Spaces, Academic Press, 1970, Chapter 11, Theorem 11.8 (as cited by the paper at that spot)

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace HardyHalfPlane

theorem cauchy_integral_formula (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    (hΦ : MemLeftHardy Φ a p) (a' : ℝ) (ha' : a' ≤ a) (g : ℝ → ℂ)
    (hg : ∀ᵐ y : ℝ ∂volume,
      Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a') (𝓝 (g y)))
    (z : ℂ) (hz : z.re ≠ a') :
    Integrable (fun y : ℝ => g y / ((a' : ℂ) + (y : ℂ) * Complex.I - z)) volume ∧
      (1 / (2 * (Real.pi : ℂ))) * ∫ y : ℝ, g y / ((a' : ℂ) + (y : ℂ) * Complex.I - z) =
        if z.re < a' then Φ z else 0 := by sorry

end HardyHalfPlane
