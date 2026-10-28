-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_exp_neg_of_lipschitz_readable
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_exp_neg_of_lipschitz_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:30.676027+00:00
-- url     : https://prove2.me/theorems/bacd1f1f-068d-4e42-88a3-d15ac6d6ee33
-- title:
--   Weak Derivative of a Negative Exponential
-- statement:
--   Let $E$ be a finite-dimensional real inner-product space with Borel structure, let $F:E\to\mathbb{R}$ be globally $L$-Lipschitz, and fix a direction $v\in E$. Then $e^{-F}$ has weak derivative along $v$ given by
--
--   $$
--   \partial_v(e^{-F})(x)=-e^{-F(x)}\,Df(x)[v],
--   $$
--
--   where $Df$ is represented by `fderiv`. Moreover, the derivative density belongs to $L^2$ on the restriction of Lebesgue measure to every compact set. No boundedness of $F$ or global integrability of $e^{-F}$ is required.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasWeakDerivAlong_exp_neg_of_lipschitz {E : Type u}
--       [instNormedAddCommGroup : NormedAddCommGroup E]
--       [instInnerProductSpace : InnerProductSpace ℝ E]
--       [instFiniteDimensional : FiniteDimensional ℝ E]
--       [instMeasurableSpace : MeasurableSpace E] [instBorelSpace : BorelSpace E]
--       {F : E → ℝ} {L : NNReal} (hF : LipschitzWith L F) (v : E) :
--       HasWeakDerivAlong (fun x => Real.exp (-F x))
--         (fun x => -Real.exp (-F x) * fderiv ℝ F x v) v ∧
--       ∀ S : Set E, IsCompact S →
--         MemLp (fun x => -Real.exp (-F x) * fderiv ℝ F x v) 2
--           ((volume : Measure E).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`hasWeakDerivAlong_of_lipschitz`](https://prove2.me/theorems/b9fc0ec0-1bac-4138-9d6d-d21b20f114b9).
--
--   Previous: [`hasWeakDerivAlong_finsetProd_of_locally_memLp_two`](https://prove2.me/theorems/9810d657-43d4-4de0-a307-1f01259642ca) · Next: [`HasWeakDerivAlong.mul_of_locally_bounded`](https://prove2.me/theorems/1133273b-c737-4c38-bf2a-2953cd23a941).
--
--   [Source excerpt, lines 567–577](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L567-L577) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L564-L659 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_exp_neg_of_lipschitz`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

universe u
open MeasureTheory Set Filter Metric

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_exp_neg_of_lipschitz_readable {E : Type u}
    [instNormedAddCommGroup : NormedAddCommGroup E]
    [instInnerProductSpace : InnerProductSpace ℝ E]
    [instFiniteDimensional : FiniteDimensional ℝ E]
    [instMeasurableSpace : MeasurableSpace E] [instBorelSpace : BorelSpace E]
    {F : E → ℝ} {L : NNReal} (hF : LipschitzWith L F) (v : E) :
    HasWeakDerivAlong (fun x => Real.exp (-F x))
      (fun x => -Real.exp (-F x) * fderiv ℝ F x v) v ∧
    ∀ S : Set E, IsCompact S →
      MemLp (fun x => -Real.exp (-F x) * fderiv ℝ F x v) 2
        ((volume : Measure E).restrict S) := by sorry
