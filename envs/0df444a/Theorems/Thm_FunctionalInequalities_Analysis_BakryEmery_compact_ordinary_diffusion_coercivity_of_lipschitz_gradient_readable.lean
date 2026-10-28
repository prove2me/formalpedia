-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_compact_ordinary_diffusion_coercivity_of_lipschitz_gradient_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.compact_ordinary_diffusion_coercivity_of_lipschitz_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:08.810994+00:00
-- url     : https://prove2.me/theorems/2333fc8d-b8d0-4b91-abd1-9ba2b3b18409
-- title:
--   Ordinary Diffusion Coercivity with Lipschitz Gradient
-- statement:
--   This is the coercivity consequence of the integrated Bochner identity at Lipschitz regularity; it is related to Lemma A.6 of Letwin (2026).
--
--   Let $E$ be a complete finite-dimensional real inner-product space with its Borel structure. Let $U:E\to\mathbb R$ be $C^1$, with $\nabla U$ Lipschitz with constant $G\in[0,\infty)$ and $U$ Lipschitz with constant $L\in[0,\infty)$. Assume $e^{-U}$ is integrable with respect to volume measure. Let $f:E\to\mathbb R$ be smooth and compactly supported, and set $\nu=\operatorname{volume}.\operatorname{tilted}(-U)$. Then:
--
--   1. The function $x\mapsto\langle D(\nabla U)(x)\nabla f(x),\nabla f(x)\rangle$ is $\nu$-integrable.
--   2. The function $x\mapsto(\mathcal L_Uf(x))^2$ is $\nu$-integrable.
--   3. The Hessian pairing is bounded above by the squared weighted Laplacian:
--
--   $$
--   \int\left\langle D(\nabla U)\nabla f,\nabla f\right\rangle d\nu
--   \leq
--   \int(\mathcal L_Uf)^2d\nu.
--   $$
--
--   This supplies an ordinary diffusion coercivity estimate without a pointwise Hessian lower bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem compact_ordinary_diffusion_coercivity_of_lipschitz_gradient
--       {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal}
--       (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
--       (hexp : Integrable (fun x => Real.exp (-U x)) (volume : Measure E))
--       {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
--       Integrable (fun x => ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫)
--         ((volume : Measure E).tilted (-U)) ∧
--       Integrable (fun x => weightedLaplacian U f x ^ 2)
--         ((volume : Measure E).tilted (-U)) ∧
--       (∫ x, ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫
--           ∂((volume : Measure E).tilted (-U))) ≤
--         ∫ x, weightedLaplacian U f x ^ 2 ∂((volume : Measure E).tilted (-U))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Bochner/Lipschitz`](https://prove2.me/theorems/0d3e8510-7673-4d06-9cae-b7b7fef307a8).
--
--   Definition modules: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Supporting theorems: [`integral_weightedLaplacian_sq_eq_of_lipschitz_gradient`](https://prove2.me/theorems/866e6109-1efa-4b77-8325-9da4c4d16ab4).
--
--   Previous: [`integral_weightedLaplacian_sq_eq_of_lipschitz_gradient`](https://prove2.me/theorems/866e6109-1efa-4b77-8325-9da4c4d16ab4).
--
--   [Source excerpt, lines 289–300](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean#L289-L300) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.6. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean#L285-L343 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Lipschitz`, declaration `FunctionalInequalities.Analysis.BakryEmery.compact_ordinary_diffusion_coercivity_of_lipschitz_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Lipschitz

open MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 2000000

theorem FunctionalInequalities.Analysis.BakryEmery.compact_ordinary_diffusion_coercivity_of_lipschitz_gradient_readable
    {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal}
    (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
    (hexp : Integrable (fun x => Real.exp (-U x)) (volume : Measure E))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    Integrable (fun x => ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫)
      ((volume : Measure E).tilted (-U)) ∧
    Integrable (fun x => weightedLaplacian U f x ^ 2)
      ((volume : Measure E).tilted (-U)) ∧
    (∫ x, ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫
        ∂((volume : Measure E).tilted (-U))) ≤
      ∫ x, weightedLaplacian U f x ^ 2 ∂((volume : Measure E).tilted (-U)) := by sorry
