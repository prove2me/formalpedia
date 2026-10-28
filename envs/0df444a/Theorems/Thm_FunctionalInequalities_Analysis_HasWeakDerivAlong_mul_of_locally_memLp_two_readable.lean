-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_mul_of_locally_memLp_two_readable
-- name    : FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_locally_memLp_two_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:06.429164+00:00
-- url     : https://prove2.me/theorems/4c31865f-283b-4c42-8cee-41884d14d427
-- title:
--   Weak Product Rule with Bounded Factors and Local Derivative Control
-- statement:
--   This is a localized weak product rule with globally essentially bounded factors. It is listed as a partial formalization of Theorem 2.5 of Letwin (arXiv:2607.24164v1).
--
--   Let $n\in\mathbb{N}$, let $f,df,g,dg$ be real-valued functions on $\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)$, and let $v$ be a vector. Assume:
--
--   1. $f$ has weak derivative $df$ along $v$, and $g$ has weak derivative $dg$ along $v$.
--   2. $f$ and $g$ belong to global $L^\infty(\operatorname{volume})$, represented by `MemLp` exponent $\top$.
--   3. For every compact $S$, $df,dg\in L^2(\operatorname{volume}|_S)$.
--
--   Then the product has weak derivative
--
--   $$x\mapsto df(x)g(x)+f(x)dg(x),$$
--
--   and this derivative belongs to $L^2(\operatorname{volume}|_S)$ for every compact $S$. This is a compact-local product theorem.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem HasWeakDerivAlong.mul_of_locally_memLp_two {n : ℕ}
--       {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
--       {v : EuclideanSpace ℝ (Fin n)}
--       (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
--       (hf_top : MemLp f (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hg_top : MemLp g (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hdf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
--       (hdg2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp dg 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
--       HasWeakDerivAlong (fun x => f x * g x)
--         (fun x => df x * g x + f x * dg x) v ∧
--       ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp (fun x => df x * g x + f x * dg x) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.mul_contDiff`](https://prove2.me/theorems/2a566c7d-243e-41f1-be35-eae8ff92ebb5), [`HasWeakDerivAlong.mul_of_memLp_two`](https://prove2.me/theorems/194c1651-5c29-4beb-84c6-06fd15f07790), [`memLp_mul_of_hasCompactSupport`](https://prove2.me/theorems/b04b1dc7-d732-49ae-8bbb-620873456903).
--
--   Previous: [`memLp_mul_of_hasCompactSupport`](https://prove2.me/theorems/b04b1dc7-d732-49ae-8bbb-620873456903) · Next: [`hasWeakDerivAlong_finsetSum_mul`](https://prove2.me/theorems/2618f40b-2846-4d7d-9e77-e6c773de9cee).
--
--   [Source excerpt, lines 211–225](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L211-L225) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L209-L344 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_locally_memLp_two`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Filter Set Metric InnerProductSpace

theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_locally_memLp_two_readable {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf_top : MemLp f (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg_top : MemLp g (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hdg2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp dg 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => f x * g x)
      (fun x => df x * g x + f x * dg x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => df x * g x + f x * dg x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
