-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_contDiff_approx_of_lipschitz_gradient_readable
-- name    : FunctionalInequalities.Analysis.exists_contDiff_approx_of_lipschitz_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:59.590532+00:00
-- url     : https://prove2.me/theorems/58f49398-895c-40bc-ab6b-62bb53052379
-- title:
--   Smooth Approximation with Uniform Gradient Control
-- statement:
--   This gives a smooth approximation scheme for a function with Lipschitz gradient.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel structure. Let $U:E\to\mathbb R$ be $C^1$, and suppose that $\nabla U$ is Lipschitz with constant $G\in[0,\infty)$. Then there exists a sequence $U_k:E\to\mathbb R$ such that:
--
--   1. Every $U_k$ is $C^\infty$.
--   2. For every $k$ and $x\in E$,
--      $$
--      \|\nabla U_k(x)-\nabla U(x)\|\leq \frac{G}{k+1}.
--      $$
--   3. Every $\nabla U_k$ is Lipschitz with the same constant $G$.
--   4. For every $x$, $U_k(x)\to U(x)$ as $k\to\infty$.
--   5. For almost every $x$ with respect to volume measure, $D(\nabla U_k)(x)$ converges to $D(\nabla U)(x)$ as $k\to\infty$.
--
--   The sequence is a reusable regularization device preserving the Lipschitz-gradient bound while providing almost-everywhere Hessian convergence.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_contDiff_approx_of_lipschitz_gradient
--       {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U)) :
--       ∃ Uk : ℕ → E → ℝ, (∀ k, ContDiff ℝ ∞ (Uk k)) ∧
--         (∀ k x, ‖gradient (Uk k) x - gradient U x‖ ≤ G / ((k : ℝ) + 1)) ∧
--         (∀ k, LipschitzWith G (gradient (Uk k))) ∧
--         (∀ x, Tendsto (fun k => Uk k x) atTop (𝓝 (U x))) ∧
--         (∀ᵐ x ∂(volume : Measure E), Tendsto (fun k => fderiv ℝ (gradient (Uk k)) x) atTop
--           (𝓝 (fderiv ℝ (gradient U) x)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Mollification/Hessian`](https://prove2.me/theorems/3226f506-ca93-41c2-b914-cd900f4c6a41).
--
--   Supporting theorems: [`hasFDerivAt_convolution_normed_of_lipschitz`](https://prove2.me/theorems/9ccb4a93-a981-4edd-a672-af4d66944fff), [`gradient_convolution_normed`](https://prove2.me/theorems/1a83f340-6b76-45bf-8d07-2b59bc9e7ab0).
--
--   Previous: [`gradient_convolution_normed`](https://prove2.me/theorems/1a83f340-6b76-45bf-8d07-2b59bc9e7ab0).
--
--   [Source excerpt, lines 268–275](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Mollification/Hessian.lean#L268-L275) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Mollification/Hessian.lean#L268-L473 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Mollification.Hessian`, declaration `FunctionalInequalities.Analysis.exists_contDiff_approx_of_lipschitz_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Hessian

open MeasureTheory Filter
open scoped Topology ContDiff
variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.exists_contDiff_approx_of_lipschitz_gradient_readable
    {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal} (hG : LipschitzWith G (gradient U)) :
    ∃ Uk : ℕ → E → ℝ, (∀ k, ContDiff ℝ ∞ (Uk k)) ∧
      (∀ k x, ‖gradient (Uk k) x - gradient U x‖ ≤ G / ((k : ℝ) + 1)) ∧
      (∀ k, LipschitzWith G (gradient (Uk k))) ∧
      (∀ x, Tendsto (fun k => Uk k x) atTop (𝓝 (U x))) ∧
      (∀ᵐ x ∂(volume : Measure E), Tendsto (fun k => fderiv ℝ (gradient (Uk k)) x) atTop
        (𝓝 (fderiv ℝ (gradient U) x))) := by sorry
