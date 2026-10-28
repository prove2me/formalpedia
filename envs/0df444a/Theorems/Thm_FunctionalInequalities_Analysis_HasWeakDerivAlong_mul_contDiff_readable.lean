-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_contDiff_readable
-- name    : FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_contDiff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:45.927993+00:00
-- url     : https://prove2.me/theorems/2a566c7d-243e-41f1-be35-eae8ff92ebb5
-- title:
--   Product Rule for Weak Directional Derivatives
-- statement:
--   This is the product rule for a weak directional derivative with a compactly supported $C^1$ multiplier.
--
--   Let $E$ be a finite-dimensional real inner-product space equipped with its Borel measurable structure. Let $f,g:E\to\mathbb{R}$ and $v\in E$. Assume `HasWeakDerivAlong f g v`, meaning that $g$ is the weak derivative of $f$ in direction $v$. Let $\chi:E\to\mathbb{R}$ be $C^1$ and compactly supported.
--
--   Then the product $\chi f$ has weak directional derivative
--
--   $$x\mapsto \chi(x)g(x)+D\chi(x)[v]f(x).$$
--
--   Here $D\chi(x)[v]$ is represented by `fderiv ℝ χ x v`. The result is a general weak-calculus lemma for localized test functions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem HasWeakDerivAlong.mul_contDiff {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v)
--       {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
--       HasWeakDerivAlong (fun x => χ x * f x) (fun x => χ x * g x + fderiv ℝ χ x v * f x) v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Previous: [`hasWeakDerivAlong_of_lipschitz`](https://prove2.me/theorems/b9fc0ec0-1bac-4138-9d6d-d21b20f114b9) · Next: [`HasWeakDerivAlong.congr_ae`](https://prove2.me/theorems/feacd1e3-2d93-4444-8c84-fe52a0849220).
--
--   [Source excerpt, lines 113–115](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Basic.lean#L113-L115) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Basic.lean#L112-L218 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Basic`, declaration `FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_contDiff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_contDiff_readable {f g : E → ℝ} {v : E} (h : HasWeakDerivAlong f g v)
    {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    HasWeakDerivAlong (fun x => χ x * f x) (fun x => χ x * g x + fderiv ℝ χ x v * f x) v := by sorry
