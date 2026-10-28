-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetSum_mul_readable
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:32.85607+00:00
-- url     : https://prove2.me/theorems/2618f40b-2846-4d7d-9e77-e6c773de9cee
-- title:
--   Finite Sums Preserve Directional Weak Derivatives
-- statement:
--   This is a calculus rule for finite linear combinations of directional weak derivatives.
--
--   Let $s$ be a finite set of indices, let $c_i\in\mathbb R$, and let $f_i,df_i:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))\to\mathbb R$. Fix a direction $v$. Assume:
--
--   1. For every $i\in s$, `df i` is the weak derivative of `f i` along $v$.
--   2. For every $i\in s$ and every compact set $S$, `df i` belongs to $L^2(S)$.
--
--   Then the finite sum has weak derivative
--
--   $$D_v\left(\sum_{i\in s}c_i f_i\right)=\sum_{i\in s}c_i df_i,$$
--
--   and the resulting derivative belongs to $L^2(S)$ for every compact $S$. The declaration `hasWeakDerivAlong_finsetSum_mul_readable` preserves the exact directional weak-derivative relation and compact-local $L^2$ membership.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasWeakDerivAlong_finsetSum_mul {n : ℕ} {ι : Type*}
--       (s : Finset ι) (c : ι → ℝ)
--       {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
--       {v : EuclideanSpace ℝ (Fin n)}
--       (hf : ∀ i ∈ s, HasWeakDerivAlong (f i) (df i) v)
--       (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
--       HasWeakDerivAlong (fun x => ∑ i ∈ s, c i * f i x)
--         (fun x => ∑ i ∈ s, c i * df i x) v ∧
--       ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp (fun x => ∑ i ∈ s, c i * df i x) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Previous: [`HasWeakDerivAlong.mul_of_locally_memLp_two`](https://prove2.me/theorems/4c31865f-283b-4c42-8cee-41884d14d427) · Next: [`hasWeakDerivAlong_finsetProd_of_locally_memLp_two`](https://prove2.me/theorems/9810d657-43d4-4de0-a307-1f01259642ca).
--
--   [Source excerpt, lines 361–372](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L361-L372) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L359-L427 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Set Filter

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetSum_mul_readable {n : ℕ} {ι : Type*}
    (s : Finset ι) (c : ι → ℝ)
    {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasWeakDerivAlong (f i) (df i) v)
    (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => ∑ i ∈ s, c i * f i x)
      (fun x => ∑ i ∈ s, c i * df i x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ i ∈ s, c i * df i x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
