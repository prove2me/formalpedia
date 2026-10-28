-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_integral_weightedLaplacian_sq_eq_of_lipschitz_gradient_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_lipschitz_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:09.091572+00:00
-- url     : https://prove2.me/theorems/866e6109-1efa-4b77-8325-9da4c4d16ab4
-- title:
--   Integrated Bochner Identity at Lipschitz Regularity
-- statement:
--   This formalizes the integrated Bochner identity for a $C^{1,1}$ potential; it is related to Lemma A.6 of Letwin (2026), cited as “Brascamp–Lieb for $\nu$.”
--
--   Let $E$ be a complete finite-dimensional real inner-product space with its Borel structure. Let $U:E\to\mathbb R$ be $C^1$, let $\nabla U$ be Lipschitz with constant $G\in[0,\infty)$, and let $U$ itself be Lipschitz with constant $L\in[0,\infty)$. Assume
--
--   1. $e^{-U}$ is integrable with respect to volume measure.
--   2. $f:E\to\mathbb R$ is $C^\infty$.
--   3. $f$ has compact support.
--
--   With $\nu=\operatorname{volume}.\operatorname{tilted}(-U)$,
--
--   $$
--   \int (\mathcal L_U f)^2\,d\nu
--   =
--   \int\left(\operatorname{HessSq}_{\mathrm{std}}(f)(x)+
--   \left\langle D(\nabla U)(x)\nabla f(x),\nabla f(x)\right\rangle\right)d\nu(x),
--   $$
--
--   where $\mathcal L_U f=\Delta f-\langle\nabla U,\nabla f\rangle$. The derivative $D(\nabla U)$ is the a.e. derivative `fderiv ℝ (gradient U)`, and the Hessian square is `hessianSqStdBasis`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_weightedLaplacian_sq_eq_of_lipschitz_gradient {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal}
--       (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
--       (hexp : Integrable (fun x => Real.exp (-U x)) (volume : Measure E))
--       {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
--       ∫ x, weightedLaplacian U f x ^ 2 ∂((volume : Measure E).tilted (-U)) =
--         ∫ x, (hessianSqStdBasis f x + ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫)
--           ∂((volume : Measure E).tilted (-U))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Bochner/Lipschitz`](https://prove2.me/theorems/0d3e8510-7673-4d06-9cae-b7b7fef307a8).
--
--   Definition modules: [`Analysis/BakryEmery/Bochner/Basic`](https://prove2.me/theorems/5602e9d0-0523-4d72-8910-f92c2e9a1b9a), [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Supporting theorems: [`gammaTwo_eq_hessianSqStdBasis_add`](https://prove2.me/theorems/179f18c6-eedc-4764-b606-7f97a6d4c71b), [`exists_contDiff_approx_of_lipschitz_gradient`](https://prove2.me/theorems/58f49398-895c-40bc-ab6b-62bb53052379).
--
--   Next: [`compact_ordinary_diffusion_coercivity_of_lipschitz_gradient`](https://prove2.me/theorems/2333fc8d-b8d0-4b91-abd1-9ba2b3b18409).
--
--   [Source excerpt, lines 131–137](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean#L131-L137) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma A.6. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean#L127-L283 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Bochner.Lipschitz`, declaration `FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_lipschitz_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Lipschitz

open MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_lipschitz_gradient_readable {U : E → ℝ} (hU : ContDiff ℝ 1 U) {G : NNReal}
    (hG : LipschitzWith G (gradient U)) {L : NNReal} (hL : LipschitzWith L U)
    (hexp : Integrable (fun x => Real.exp (-U x)) (volume : Measure E))
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∫ x, weightedLaplacian U f x ^ 2 ∂((volume : Measure E).tilted (-U)) =
      ∫ x, (hessianSqStdBasis f x + ⟪fderiv ℝ (gradient U) x (gradient f x), gradient f x⟫)
        ∂((volume : Measure E).tilted (-U)) := by sorry
