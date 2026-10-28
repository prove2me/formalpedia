-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_eq_norm_gradient_readable
-- name    : FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:16.658272+00:00
-- url     : https://prove2.me/theorems/aae816d4-9490-473e-9f62-e3c0294c7ffc
-- title:
--   Local Slope Equals Gradient Norm
-- statement:
--   This is the pointwise identification of the one-moving-point local slope with the canonical Hilbert-space gradient norm.
--
--   Let $E$ be a complete real inner-product normed space, let $f:E\to\mathbb R$, and let $x\in E$. Assume that $f$ is Fréchet differentiable at $x$. Then the local slope `apply` of $f$ at $x$ equals the extended nonnegative real number obtained from the norm of the gradient:
--
--   $$
--   \operatorname{apply}(f,x)=\operatorname{ENNReal.ofReal}\bigl(\|\nabla f(x)\|\bigr).
--   $$
--
--   Here $\nabla f(x)$ is the canonical Hilbert gradient and the right-hand side is an `ENNReal` value in $[0,\infty]$. The Lean declaration is `apply_eq_norm_gradient_readable`; no nontriviality assumption on $E$ or on the derivative is imposed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.LocalSlope`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem apply_eq_norm_gradient
--       (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
--       apply f x = ENNReal.ofReal ‖gradient f x‖
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/LocalSlope/Gradient`](https://prove2.me/theorems/d01ba6e3-090e-46a3-a175-38f38d850838).
--
--   Definition modules: [`Energy/LocalSlope/Basic`](https://prove2.me/theorems/403376af-90fc-4aef-aed0-aefc10593586).
--
--   Next: [`admissible_iff_memLp_gradient`](https://prove2.me/theorems/284b0183-bfda-452b-b5ff-2efd469c4a7d).
--
--   [Source excerpt, lines 31–33](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/LocalSlope/Gradient.lean#L31-L33) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/LocalSlope/Gradient.lean#L29-L84 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.LocalSlope.Gradient`, declaration `FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_LocalSlope_Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient_readable
    (f : E → ℝ) (x : E) (hf : DifferentiableAt ℝ f x) :
    apply f x = ENNReal.ofReal ‖gradient f x‖ := by sorry
