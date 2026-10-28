-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_memLp_two_readable
-- name    : FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_memLp_two_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:10.124536+00:00
-- url     : https://prove2.me/theorems/194c1651-5c29-4beb-84c6-06fd15f07790
-- title:
--   Weak Product Rule Under Global $L^2$ Bounds
-- statement:
--   This is the scalar weak product rule under global $L^2$ hypotheses. It is listed as a partial formalization of Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $n\in\mathbb{N}$, let $f,df,g,dg:\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)\to\mathbb{R}$, and let $v$ be a vector in that space. Assume:
--
--   1. `HasWeakDerivAlong f df v`.
--   2. `HasWeakDerivAlong g dg v`.
--   3. $f,df,g,dg$ all belong to global $L^2(\operatorname{volume})$.
--
--   Then
--
--   $$\operatorname{HasWeakDerivAlong}\bigl(x\mapsto f(x)g(x),\ x\mapsto df(x)g(x)+f(x)dg(x),\ v\bigr).$$
--
--   The conclusion is a weak directional derivative statement for the product, with no almost-everywhere qualification added to the displayed representative.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem HasWeakDerivAlong.mul_of_memLp_two {n : ℕ}
--       {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
--       {v : EuclideanSpace ℝ (Fin n)}
--       (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
--       (hf2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hdf2 : MemLp df 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hg2 : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hdg2 : MemLp dg 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
--       HasWeakDerivAlong (fun x => f x * g x)
--         (fun x => df x * g x + f x * dg x) v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`lintegral_enorm_convolution_sq_le`](https://prove2.me/theorems/63807bea-13bd-4a60-93ed-c5b5453cd20a), [`tendsto_eLpNorm_convolution_sub`](https://prove2.me/theorems/3e5007ce-6906-4a04-82a9-55a0bdd821b3), [`fderiv_convolution_eq_of_hasWeakDerivAlong`](https://prove2.me/theorems/21b92288-9077-4db1-9b99-ee62a25b6a04).
--
--   Next: [`memLp_mul_of_hasCompactSupport`](https://prove2.me/theorems/b04b1dc7-d732-49ae-8bbb-620873456903).
--
--   [Source excerpt, lines 55–64](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L55-L64) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L52-L181 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_memLp_two`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Filter Set Metric InnerProductSpace
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_memLp_two_readable {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : MemLp df 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg2 : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdg2 : MemLp dg 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v := by sorry
