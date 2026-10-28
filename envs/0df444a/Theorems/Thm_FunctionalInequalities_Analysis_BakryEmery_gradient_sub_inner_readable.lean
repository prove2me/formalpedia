-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_gradient_sub_inner_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.gradient_sub_inner_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:54.997888+00:00
-- url     : https://prove2.me/theorems/6e39480b-596b-4064-876c-d786d322b2b9
-- title:
--   Gradient of a Linear Perturbation
-- statement:
--   This pointwise differential identity computes the gradient after subtracting a linear functional.
--
--   Let $E$ be a complete real inner-product space, let $V:E\to\mathbb R$, and let $z,x\in E$. If $V$ is differentiable at $x$, then
--
--   $$\nabla\bigl(V-\langle z,\cdot\rangle\bigr)(x)=\nabla V(x)-z.$$
--
--   The statement uses `gradient` and requires only differentiability of $V$ at the specified point. It is the basic calculus identity used when differentiating tilted potentials.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gradient_sub_inner {V : E → ℝ} (z x : E) (hV : DifferentiableAt ℝ V x) :
--       gradient (fun y => V y - ⟪z, y⟫) x = gradient V x - z
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Next: [`expTilt_tilted`](https://prove2.me/theorems/b77ce921-0d7b-4b31-ac8b-28afb215f4d2).
--
--   [Source excerpt, lines 61–62](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L61-L62) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L59-L78 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.gradient_sub_inner`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic

open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.gradient_sub_inner_readable {V : E → ℝ} (z x : E) (hV : DifferentiableAt ℝ V x) :
    gradient (fun y => V y - ⟪z, y⟫) x = gradient V x - z := by sorry
