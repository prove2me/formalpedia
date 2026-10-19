-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_integral_schwartz_quadratic_exact
-- name    : OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_quadratic_exact
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:27:42.545004+00:00
-- url     : https://prove2.me/theorems/9c2f96d3-3268-4c2f-858e-48169e2f6dcf
-- title:
--   Exact Fourier identity for a Schwartz function against an undamped quadratic chirp
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{C}$ be a Schwartz function with inverse Fourier transform $\check f(\xi)=\int_{\mathbb{R}}f(x)\,e^{2\pi i x\xi}\,dx$. Let $t$ be a nonzero real number and $u\in\mathbb{R}$. Then
--   $$
--   \int_{\mathbb{R}}f(x)\,e^{\,i(\pi t x^2-2\pi u x)}\,dx=\frac{1}{(-it)^{1/2}}\int_{\mathbb{R}}\check f(\xi)\,e^{-i\pi(\xi+u)^2/t}\,d\xi,
--   $$
--   where $(-it)^{1/2}$ is the principal square root; explicitly $(-it)^{1/2}=\sqrt{|t|}\,e^{-i\pi\operatorname{sign}(t)/4}$.
--
--   This is the quadratic Fourier identity for a pure chirp of curvature $t$, without any Gaussian damping. The right-hand side carries the curvature only through the prefactor of modulus $|t|^{-1/2}$ and the multiplier $e^{-i\pi(\xi+u)^2/t}$, which is close to a linear phase when $|t|$ is large; this is the starting point of a stationary-phase expansion with an error that is uniform in the linear frequency $u$.
--
--   **Formalization Note** $f$ is an element of `𝓢(ℝ, ℂ)` and $\check f$ is `𝓕⁻ f`; the phases are written with `realPhase x` $=e^{ix}$, and the prefactor is `1 / (-Complex.I * t) ^ (1 / 2 : ℂ)` with the principal complex power.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Gaussian.lean#L154-L180

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian

open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.integral_schwartz_quadratic_exact (f : 𝓢(ℝ, ℂ))
    {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    (∫ x : ℝ, f x * realPhase (Real.pi * t * x ^ 2 - 2 * Real.pi * u * x)) =
    1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) *
      ∫ ξ : ℝ, (𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ * realPhase (-Real.pi / t * (ξ + u) ^ 2) := by sorry
