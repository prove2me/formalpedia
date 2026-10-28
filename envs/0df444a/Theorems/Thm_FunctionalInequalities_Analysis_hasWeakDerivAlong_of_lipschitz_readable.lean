-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_lipschitz_readable
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:24.440812+00:00
-- url     : https://prove2.me/theorems/b9fc0ec0-1bac-4138-9d6d-d21b20f114b9
-- title:
--   Weak Directional Derivative of a Lipschitz Function
-- statement:
--   This is a weak-derivative form of the almost-everywhere differentiability theorem for Lipschitz functions.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $f:E\to\mathbb R$, and let $L\in[0,\infty)$ be a Lipschitz constant. If $f$ is $L$-Lipschitz, then for every direction $v\in E$, the function
--   $$x\longmapsto Df(x)[v]$$
--   with `fderiv` interpreted pointwise is a weak derivative of $f$ in direction $v$. Equivalently, it satisfies the weak directional integration-by-parts identity against the test functions occurring in `HasWeakDerivAlong`.
--
--   The result provides the weak derivative interface needed to use Rademacher derivatives in integration-by-parts arguments.
--
--   **Formalization Note.** The conclusion is the predicate `HasWeakDerivAlong`; the derivative is the pointwise Fréchet derivative, and the identification is understood in the almost-everywhere sense with respect to volume measure.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasWeakDerivAlong_of_lipschitz {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) (v : E) :
--       HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Previous: [`hasWeakDerivAlong_of_contDiff`](https://prove2.me/theorems/4e2a811d-5127-4a66-87f8-6417e73ed552) · Next: [`HasWeakDerivAlong.mul_contDiff`](https://prove2.me/theorems/2a566c7d-243e-41f1-be35-eae8ff92ebb5).
--
--   [Source excerpt, lines 71–72](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Basic.lean#L71-L72) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Basic.lean#L70-L110 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Basic`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_readable {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) (v : E) :
    HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v := by sorry
