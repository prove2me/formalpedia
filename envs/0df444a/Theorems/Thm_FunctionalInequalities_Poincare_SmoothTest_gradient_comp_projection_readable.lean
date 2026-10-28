-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_gradient_comp_projection_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.gradient_comp_projection_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:36.107215+00:00
-- url     : https://prove2.me/theorems/1d27c79a-04ce-4f28-998e-35a7f0d8fec0
-- title:
--   Gradient Chain Rule for a Continuous Linear Map
-- statement:
--   This is a technical gradient chain rule for composition with a continuous linear map.
--
--   Let $E$ and $F$ be complete real inner-product normed additive groups, and let $q:E\to F$ be a continuous linear map. Let $f:F\to\mathbb R$ and $x\in E$, and assume that $f$ is differentiable at $q(x)$. Then
--
--   $$
--   \nabla(f\circ q)(x)=q^*\bigl(\nabla f(q(x))\bigr),
--   $$
--
--   where $q^*:F\to E$ is the Hilbert-space adjoint of $q$.
--
--   The result provides the differential identity needed to transport smooth test functions and their gradient energies between inner-product spaces.
--
--   **Formalization Note**: The map is represented by `ContinuousLinearMap`, its adjoint by `q.adjoint`, and the conclusion uses the Mathlib `gradient`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gradient_comp_projection {f : F → ℝ} {x : E}
--       (hf : DifferentiableAt ℝ f (q x)) :
--       gradient (f ∘ q) x = q.adjoint (gradient f (q x))
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/SmoothTest/Transport`](https://prove2.me/theorems/f97165f6-9a6a-4e3a-aff4-a4bd22cfc6b6).
--
--   Next: [`admissible_map_linearIsometryEquiv_iff`](https://prove2.me/theorems/efd61af4-c91b-48fd-a2eb-046306bcfae2).
--
--   [Source excerpt, lines 47–49](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean#L47-L49) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean#L44-L61 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.Transport`, declaration `FunctionalInequalities.Poincare.SmoothTest.gradient_comp_projection`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Transport

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable (q : E →L[ℝ] F)

theorem FunctionalInequalities.Poincare.SmoothTest.gradient_comp_projection_readable {f : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (q x)) :
    gradient (f ∘ q) x = q.adjoint (gradient f (q x)) := by sorry
