-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_inner_iteratedFDeriv_gradient_apply_408915f
-- name    : FunctionalInequalities.Analysis.inner_iteratedFDeriv_gradient_apply_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:03:37.128999+00:00
-- url     : https://prove2.me/theorems/af906c88-494e-4f9f-8193-d22ccce1fb79
-- title:
--   Gradient Jets Pair With the Next Derivative
-- statement:
--   This is a calculus identity relating iterated derivatives of a gradient to the next iterated derivative of the original function.
--
--   Let $E$ be a complete real inner-product space, and let $f : E \to \mathbb{R}$ be infinitely differentiable, expressed by the hypothesis `ContDiff ℝ ∞ f`. For every natural number $r$, point $x \in E$, direction family $h : \operatorname{Fin}(r) \to E$, and additional direction $w \in E$, the inner product of the $r$-th iterated derivative of the gradient with $w$ equals the $(r+1)$-st iterated derivative of $f$, evaluated on the directions in $h$ followed by $w$:
--
--   $$
--   \left\langle D^r(\nabla f)(x)[h], w \right\rangle
--   = D^{r+1}f(x)[h,w].
--   $$
--
--   Here `gradient` denotes the gradient of $f$, `iteratedFDeriv` denotes the iterated Fréchet derivative, and `Fin.snoc h w` appends $w$ as the final direction to the family $h$.
--
--   This is a reusable identity for converting gradient-jet expressions into higher derivatives of a scalar-valued function, with no restriction on the order $r$ or the dimension of $E$.
--
--   **Formalization Note** The derivatives are real Fréchet derivatives, the inner product is the real inner product on the complete space $E$, and the equality is pointwise for every choice of $r$, $x$, $h$, and $w$.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/GradientJet.lean#L53-L80 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.GradientJet`, declaration `FunctionalInequalities.Analysis.inner_iteratedFDeriv_gradient_apply`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

noncomputable section
open scoped RealInnerProductSpace ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section GradientJet
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FunctionalInequalities.Analysis.inner_iteratedFDeriv_gradient_apply_408915f {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℕ) (x : E)
    (h : Fin r → E) (w : E) :
    ⟪iteratedFDeriv ℝ r (gradient f) x h, w⟫ = iteratedFDeriv ℝ (r + 1) f x (Fin.snoc h w) := by sorry
