-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_gradient_comp_projection_408915f
-- name    : FunctionalInequalities.Poincare.SmoothTest.gradient_comp_projection_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:38:37.595988+00:00
-- url     : https://prove2.me/theorems/b5964ea4-0102-415f-b6d7-ee14f83d4f7a
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean#L44-L61 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.Transport`, declaration `FunctionalInequalities.Poincare.SmoothTest.gradient_comp_projection`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
section CoordinateLift
variable (q : E →L[ℝ] F)

theorem FunctionalInequalities.Poincare.SmoothTest.gradient_comp_projection_408915f {f : F → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (q x)) :
    gradient (f ∘ q) x = q.adjoint (gradient f (q x)) := by sorry
