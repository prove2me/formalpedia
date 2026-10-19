-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_uniform_quadratic_integration
-- name    : OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_integration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:28:56.591308+00:00
-- url     : https://prove2.me/theorems/0c78af17-32cb-41e4-a41c-958844105a4b
-- title:
--   Stationary phase for a quadratic chirp with an error bound uniform in the frequency shift
-- statement:
--   Let $g\colon\mathbb{R}\to\mathbb{C}$ be an infinitely differentiable function with compact support, and let $\check g(\xi)=\int_{\mathbb{R}} g(x)\,e^{2\pi i x\xi}\,dx$ be its inverse Fourier transform (a Schwartz function). Let $\beta\neq 0$ and $T>0$ be real numbers, let $u\in\mathbb{R}$, and write $\operatorname{sgn}\beta\in\{-1,1\}$ for the sign of $\beta$. Then there is a complex number $E$ such that
--
--   $$
--   \int_{\mathbb{R}} g(x)\,e^{2\pi i\left(\frac{T\beta x^{2}}{2}-ux\right)}\,dx=\frac{e^{2\pi i\left(\frac{\operatorname{sgn}\beta}{8}-\frac{u^{2}}{2T\beta}\right)}}{\sqrt{T|\beta|}}\left(g\!\left(\frac{u}{T\beta}\right)+E\right)
--   $$
--
--   and
--
--   $$
--   |E|\le\frac{\pi}{T|\beta|}\int_{\mathbb{R}}\xi^{2}\,|\check g(\xi)|\,d\xi .
--   $$
--
--   This is a stationary-phase formula for a smooth bump integrated against the quadratic chirp $x\mapsto e^{2\pi i(T\beta x^2/2-ux)}$. The main term is the value of $g$ at the stationary point $x_0=u/(T\beta)$ of the phase, multiplied by the Fresnel factor $e^{\pi i\operatorname{sgn}\beta/4}/\sqrt{T|\beta|}$ and a unimodular phase; the relative error is $O(1/T)$ with a constant depending only on $g$ and $\beta$, and the bound is the same for every shift $u$. In the flat Littlewood polynomial construction it gives precise control of the size of Fourier coefficients of quadratically modulated smooth profiles.
--
--   **Formalization Note** The phase is written with `realPhase θ = exp(iθ)`, $g$ is regarded as a Schwartz function via `HasCompactSupport.toSchwartzMap`, and $\check g$ is Mathlib's inverse Fourier transform `𝓕⁻`, whose convention is $\check g(\xi)=\int g(x)e^{2\pi i x\xi}\,dx$. The sign is `Real.sign`, which is $\pm1$ here because $\beta\neq0$. In Lean the error bound is written as $\big(\tfrac{\pi}{|\beta|}\int\xi^2|\check g(\xi)|\,d\xi\big)/T$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Gaussian.lean#L320-L348

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian

open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.uniform_quadratic_integration (g : ℝ → ℂ) (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {β : ℝ} (hβ : β ≠ 0) {T : ℝ} (hT : 0 < T) (u : ℝ) :
    ∃ E : ℂ,
      ‖E‖ ≤ (Real.pi / |β| * (∫ ξ : ℝ, ξ ^ 2 *
        ‖(𝓕⁻ (hg.toSchwartzMap hgs) : 𝓢(ℝ, ℂ)) ξ‖)) / T ∧
      (∫ x : ℝ, g x * realPhase (2 * Real.pi * (T * β * x ^ 2 / 2 - u * x))) =
        (realPhase (2 * Real.pi * (Real.sign β / 8 - u ^ 2 / (2 * T * β))) /
          (Real.sqrt (T * |β|) : ℂ)) * (g (u / (T * β)) + E) := by sorry
