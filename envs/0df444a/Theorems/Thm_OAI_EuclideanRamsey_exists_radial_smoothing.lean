-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_exists_radial_smoothing
-- name    : OAI.EuclideanRamsey.exists_radial_smoothing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T01:58:57.58927+00:00
-- url     : https://prove2.me/theorems/fac7e889-e2ea-43f6-9555-b2457225e2f5
-- title:
--   Smooth nonnegative bumps whose Laplacian has arbitrarily small weighted negative part
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $n\ge1$, equipped with its Borel $\sigma$-algebra and an additive Haar measure $\mu$. For $f:E\to\mathbb{R}$ let $\tfrac12\Delta f(x)=\tfrac12\sum_{k=1}^nD^2f(x)[e_k,e_k]$ be the half-Laplacian, computed in a fixed orthonormal basis $e_1,\dots,e_n$, where $D^2f(x)$ is the second Fréchet derivative.
--
--   For every $\eta>0$ there is a function $b:E\to\mathbb{R}$ such that $b$ is infinitely differentiable, has compact support, satisfies $b(x)\ge0$ for all $x$ and $\int_Eb\,d\mu>0$, and
--   $$\int_E\max\Bigl(-\tfrac12\Delta b(x),\,0\Bigr)\,\|x\|^2\,d\mu(x)\;<\;\eta\int_Eb\,d\mu .$$
--
--   So the negative part of the Laplacian of a smooth bump, weighted by $\|x\|^2$, can be made an arbitrarily small fraction of the bump's mass. Such bumps serve as smoothing kernels in the differential splitting step of the Euclidean Ramsey argument, where second-order Taylor errors must be dominated by the mass of the kernel.
--
--   **Formalization Note** Smoothness is `ContDiff ℝ (⊤ : ℕ∞) b`, compact support is `HasCompactSupport b`, the measure satisfies `μ.IsAddHaarMeasure` with `[BorelSpace E]`, and the integrals are Bochner integrals; all integrands here are continuous with compact support, so the convention that non-integrable functions integrate to $0$ plays no role. The dimension hypothesis is `1 ≤ Module.finrank ℝ E`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/SmoothingKernel.lean#L437-L475

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel

open OAI OAI.EuclideanRamsey
universe uDomain
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
variable {E : Type uDomain} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

theorem OAI.EuclideanRamsey.exists_radial_smoothing (hn : 1 ≤ Module.finrank ℝ E) {η : ℝ} (hη : 0 < η) :
    ∃ b : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) b ∧ HasCompactSupport b ∧
      (∀ x, 0 ≤ b x) ∧ 0 < ∫ x, b x ∂μ ∧
      (∫ x, max (-halfLaplacian b x) 0 * ‖x‖^2 ∂μ) < η * ∫ x, b x ∂μ := by sorry
