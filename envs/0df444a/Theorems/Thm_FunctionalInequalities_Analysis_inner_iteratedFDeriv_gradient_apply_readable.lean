-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_inner_iteratedFDeriv_gradient_apply_readable
-- name    : FunctionalInequalities.Analysis.inner_iteratedFDeriv_gradient_apply_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:54.33676+00:00
-- url     : https://prove2.me/theorems/98bdd014-ddd3-4c09-a9f1-90cc5a041bc5
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_iteratedFDeriv_gradient_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℕ) (x : E)
--       (h : Fin r → E) (w : E) :
--       ⟪iteratedFDeriv ℝ r (gradient f) x h, w⟫ = iteratedFDeriv ℝ (r + 1) f x (Fin.snoc h w)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/IteratedDerivative/GradientJet`](https://prove2.me/theorems/2f9ce587-2ee9-4125-9ef5-333d09ad8523).
--
--   Previous: [`iteratedFDeriv_sub_const_of_pos`](https://prove2.me/theorems/5eae9d29-35ba-4434-ad2d-a584e6ef24b4).
--
--   [Source excerpt, lines 55–57](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/IteratedDerivative/GradientJet.lean#L55-L57) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/GradientJet.lean#L53-L80 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.GradientJet`, declaration `FunctionalInequalities.Analysis.inner_iteratedFDeriv_gradient_apply`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_GradientJet

open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem FunctionalInequalities.Analysis.inner_iteratedFDeriv_gradient_apply_readable {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (r : ℕ) (x : E)
    (h : Fin r → E) (w : E) :
    ⟪iteratedFDeriv ℝ r (gradient f) x h, w⟫ = iteratedFDeriv ℝ (r + 1) f x (Fin.snoc h w) := by sorry
