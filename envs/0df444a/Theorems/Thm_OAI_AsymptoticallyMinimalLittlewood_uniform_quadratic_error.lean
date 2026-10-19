-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_uniform_quadratic_error
-- name    : OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:28:24.719696+00:00
-- url     : https://prove2.me/theorems/360c2324-5f4d-4d50-b2bf-d387718232a0
-- title:
--   Stationary phase for a quadratic chirp with an explicit error uniform in the linear frequency
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{C}$ be a Schwartz function with inverse Fourier transform $\check f(\xi)=\int_{\mathbb{R}}f(x)\,e^{2\pi i x\xi}\,dx$, let $t$ be a nonzero real number and $u\in\mathbb{R}$. Then there is a complex number $E$ with
--   $$
--   |E|\le\frac{\pi}{|t|}\int_{\mathbb{R}}\xi^2\,|\check f(\xi)|\,d\xi
--   $$
--   such that
--   $$
--   \int_{\mathbb{R}}f(x)\,e^{\,i(\pi t x^2-2\pi u x)}\,dx=\frac{e^{-i\pi u^2/t}}{(-it)^{1/2}}\Bigl(f\Bigl(\frac ut\Bigr)+E\Bigr),
--   $$
--   where $(-it)^{1/2}$ is the principal square root.
--
--   The phase $\pi t x^2-2\pi u x$ is stationary at $x=u/t$, and the theorem is a stationary-phase formula with an explicit remainder: the main term is the value of $f$ at the stationary point times a prefactor of modulus $|t|^{-1/2}$, and the relative error is $O(1/|t|)$ with a constant that depends on $f$ only through the second moment of $|\check f|$, uniformly in the linear frequency $u$. After rescaling it evaluates the Fourier coefficients of smooth chirps that appear when sampled quadratic exponential sums are treated by Poisson summation.
--
--   **Formalization Note** $f$ is an element of `𝓢(ℝ, ℂ)` and $\check f$ is `𝓕⁻ f`; the phases are written with `realPhase x` $=e^{ix}$, so the prefactor is `1 / (-Complex.I * t) ^ (1 / 2 : ℂ) * realPhase (-Real.pi / t * u ^ 2)`. The integral in the bound is finite because $\check f$ is a Schwartz function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Gaussian.lean#L208-L269

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian

open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_error (f : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : t ≠ 0) (u : ℝ) :
    ∃ E : ℂ,
      ‖E‖ ≤ Real.pi / |t| * (∫ ξ : ℝ, ξ ^ 2 * ‖(𝓕⁻ f : 𝓢(ℝ, ℂ)) ξ‖) ∧
      (∫ x : ℝ, f x * realPhase (Real.pi * t * x ^ 2 - 2 * Real.pi * u * x)) =
        (1 / (-Complex.I * (t : ℂ)) ^ (1 / 2 : ℂ) *
          realPhase (-Real.pi / t * u ^ 2)) * (f (u / t) + E) := by sorry
