-- Prove2me | Theorems.Thm_HardyHalfPlane_tendsto_eLpNorm_sub_boundary_function
-- name    : HardyHalfPlane.tendsto_eLpNorm_sub_boundary_function
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-22T19:22:23.941127+00:00
-- url     : https://prove2.me/theorems/e2044d52-0eb6-4a99-abfb-e0b2830905b5
-- title:
--   Functions in $H^p(\mathbf C_{<a})$, $1\le p<\infty$, converge in $L^p$ to their boundary function on the line $\operatorname{Re}(s)=a$
-- statement:
--   **Boundary values of $H^p$ functions on a half-plane are attained in $L^p$.** Let $a\in\mathbb R$, let $1\le p<\infty$, and let $\Phi\in H^p(\mathbf C_{<a})$: the function $\Phi$ is holomorphic on the half-plane $\mathbf C_{<a}=\{s\in\mathbb C:\operatorname{Re}(s)<a\}$ and
--
--   $$\|\Phi\|_{H^p(\mathbf C_{<a})}=\sup_{\sigma<a}\Bigl(\int_{\mathbb R}|\Phi(\sigma+iy)|^p\,\mathrm dy\Bigr)^{1/p}<\infty .$$
--
--   Let $g:\mathbb R\to\mathbb C$ be a boundary function of $\Phi$, that is
--
--   $$g(y)=\lim_{\sigma\to a^-}\Phi(\sigma+iy)\qquad\text{for almost every }y\in\mathbb R .$$
--
--   Then the functions $y\mapsto\Phi(\sigma+iy)$ converge to $g$ in $L^p(\mathbb R)$ as $\sigma\to a^-$:
--
--   $$\lim_{\sigma\to a^-}\int_{\mathbb R}|\Phi(\sigma+iy)-g(y)|^p\,\mathrm dy=0 .$$
--
--   This is the classical theorem that a function of the Hardy space of a half-plane attains its boundary values in the $L^p$ norm (P. Duren, *Theory of $H^p$ Spaces*, Ch. 11, where the upper half-plane is used; for $p=1$ it rests on the F. and M. Riesz theorem). The source recalls the boundary function $f_\Phi$ of $\Phi\in H^p(\mathbf C_{<a})$ and the isometric embedding $H^p(\mathbf C_{<a})\to L^p(\mathbb R)$ in §B.2.1; the $L^p$ convergence is what allows identities proved on the lines $\operatorname{Re}(s)=\sigma<a$, such as the Cauchy integral formula, to be passed to the boundary line $\operatorname{Re}(s)=a$.
--
--   **Formalization Note.** `HardyHalfPlane.MemLeftHardy Φ a p` is the membership predicate of the accompanying definition file (holomorphy on `{s | s.re < a}` and finiteness of `leftHardyNorm Φ a p`). The exponent is `p : ℝ≥0∞` with `1 ≤ p` and `p ≠ ⊤`. The boundary function `g` is any function that is almost everywhere the limit of `Φ (σ + y i)` as `σ → a⁻` (filter `𝓝[<] a`); its existence is a separate theorem. The $L^p$ distance is Mathlib's `eLpNorm` (with values in `[0, ∞]`) with respect to Lebesgue measure.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 592, §B.2.1 (Cauchy integral formulas for $\Phi\in H^p(\mathbf C_{<a})$, recalled from [Dur, Ch. 11, Thm. 11.8]); auxiliary lemma for the proof of HardyHalfPlane.cauchy_integral_formula; classical reference: P. Duren, Theory of $H^p$ Spaces, Academic Press, 1970, Chapter 11 ($H^p$ spaces over a half-plane)

import Mathlib
import Definitions.Def_HardyHalfPlane_LeftHardy

open MeasureTheory Filter Topology
open scoped ENNReal

set_option autoImplicit false

namespace HardyHalfPlane

theorem tendsto_eLpNorm_sub_boundary_function (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) (hp1 : 1 ≤ p)
    (hp : p ≠ ⊤) (hΦ : MemLeftHardy Φ a p) (g : ℝ → ℂ)
    (hg : ∀ᵐ y : ℝ ∂volume,
      Tendsto (fun σ : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) (𝓝[<] a) (𝓝 (g y))) :
    Tendsto (fun σ : ℝ => eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I) - g y) p volume)
      (𝓝[<] a) (𝓝 0) := by sorry

end HardyHalfPlane
