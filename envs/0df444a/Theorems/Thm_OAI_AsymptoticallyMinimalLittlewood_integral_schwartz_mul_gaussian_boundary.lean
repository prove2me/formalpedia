-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_integral_schwartz_mul_gaussian_boundary
-- name    : OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_mul_gaussian_boundary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:26:48.871126+00:00
-- url     : https://prove2.me/theorems/05715a58-aaec-4de9-be0e-c18b42c97c9c
-- title:
--   Gaussian Fourier identity for Schwartz functions on the closed right half-plane $\operatorname{Re} b\ge 0$
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{C}$ be a Schwartz function and let $\check f$ be its inverse Fourier transform, $\check f(\xi)=\int_{\mathbb{R}}f(x)\,e^{2\pi i x\xi}\,dx$. Let $b\in\mathbb{C}$ with $\operatorname{Re}b\ge0$ and $b\ne0$, and let $u\in\mathbb{R}$. Then
--   $$
--   \int_{\mathbb{R}}f(x)\,\exp\bigl(-\pi b x^2-2\pi i u x\bigr)\,dx=\frac{1}{b^{1/2}}\int_{\mathbb{R}}\check f(\xi)\,\exp\Bigl(-\frac{\pi}{b}(\xi+u)^2\Bigr)\,d\xi,
--   $$
--   where $b^{1/2}=\exp\bigl(\tfrac12\operatorname{Log}b\bigr)$ is the principal branch of the square root.
--
--   The identity is classical for damped Gaussians, $\operatorname{Re}b>0$. Its value here is that it also covers the boundary of the half-plane, in particular purely imaginary $b=-it$ with $t\in\mathbb{R}\setminus\{0\}$, where $\exp(-\pi b x^2)$ is an undamped chirp of modulus one. In that form it is the exact identity behind the stationary-phase evaluation of quadratic oscillatory integrals.
--
--   **Formalization Note** $f$ is an element of `𝓢(ℝ, ℂ)`, $\check f$ is `𝓕⁻ f` viewed as a Schwartz map (Mathlib's normalization with $e^{2\pi i x\xi}$), and $b^{1/2}$ is `b ^ (1 / 2 : ℂ)` (`Complex.cpow`). Both integrands are integrable because the exponential kernels have modulus at most one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Gaussian.lean#L63-L136

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian

open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_mul_gaussian_boundary
    (f : 𝓢(ℝ, ℂ)) {b : ℂ} (hb : 0 ≤ b.re) (hb0 : b ≠ 0) (u : ℝ) :
    (∫ x : ℝ, f x * Complex.exp (-Real.pi * b * (x : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * u * x)) =
    1 / b ^ (1 / 2 : ℂ) * ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ *
      Complex.exp (-Real.pi / b * ((ξ : ℂ) + u) ^ 2) := by sorry
