-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_of_contDiff_readable
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:41.282566+00:00
-- url     : https://prove2.me/theorems/4e2a811d-5127-4a66-87f8-6417e73ed552
-- title:
--   Classical Derivatives Give Weak Directional Derivatives
-- statement:
--   This is the identification of classical and weak directional derivatives.
--
--   Let $E$ be a finite-dimensional real inner-product space with measurable and Borel structures, let $f:E\to\mathbb R$ be $C^1$, and fix $v\in E$. Then `fderiv ℝ f x v` is a weak derivative of $f$ along $v$:
--
--   $$D_v^{\mathrm{weak}}f(x)=Df(x)v.$$
--
--   In Lean this is expressed as `HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v`. The result includes the local integrability conditions required by the weak derivative interface.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasWeakDerivAlong_of_contDiff {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) :
--       HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Next: [`hasWeakDerivAlong_of_lipschitz`](https://prove2.me/theorems/b9fc0ec0-1bac-4138-9d6d-d21b20f114b9).
--
--   [Source excerpt, lines 43–44](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Basic.lean#L43-L44) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Basic.lean#L41-L68 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Basic`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_of_contDiff_readable {f : E → ℝ} (hf : ContDiff ℝ 1 f) (v : E) :
    HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v := by sorry
