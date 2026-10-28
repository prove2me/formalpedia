-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_finsetProd_of_locally_memLp_two_readable
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetProd_of_locally_memLp_two_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:33.48924+00:00
-- url     : https://prove2.me/theorems/9810d657-43d4-4de0-a307-1f01259642ca
-- title:
--   Weak Leibniz Rule for Finite Products
-- statement:
--   This is a weak finite-product Leibniz rule on $\mathbb{R}^n$.
--
--   Let $s$ be a finite set of indices, let $f_i$ and $df_i$ be real-valued functions, and let $v$ be a direction. Assume for every $i\in s$ that $f_i$ has weak derivative $df_i$ along $v$, each $f_i$ belongs to $L^{\infty}$ with respect to Lebesgue measure, and each $df_i$ belongs locally to $L^2$ on compact sets. Then the product has weak derivative
--
--   $$
--   \partial_v\!\left(\prod_{i\in s}f_i\right)
--   =\sum_{i\in s}df_i\prod_{j\in s\setminus\{i\}}f_j,
--   $$
--
--   and the displayed derivative belongs locally to $L^2$ on every compact set. The assertion includes the empty-product case.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasWeakDerivAlong_finsetProd_of_locally_memLp_two {n : ℕ} {ι : Type*}
--       [DecidableEq ι] (s : Finset ι)
--       {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
--       {v : EuclideanSpace ℝ (Fin n)}
--       (hf : ∀ i ∈ s, HasWeakDerivAlong (f i) (df i) v)
--       (hbound : ∀ i ∈ s, MemLp (f i) (⊤ : ENNReal)
--         (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
--       HasWeakDerivAlong (fun x => ∏ i ∈ s, f i x)
--         (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) v ∧
--       ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.mul_of_locally_memLp_two`](https://prove2.me/theorems/4c31865f-283b-4c42-8cee-41884d14d427), [`hasWeakDerivAlong_of_contDiff`](https://prove2.me/theorems/4e2a811d-5127-4a66-87f8-6417e73ed552).
--
--   Previous: [`hasWeakDerivAlong_finsetSum_mul`](https://prove2.me/theorems/2618f40b-2846-4d7d-9e77-e6c773de9cee) · Next: [`hasWeakDerivAlong_exp_neg_of_lipschitz`](https://prove2.me/theorems/bacd1f1f-068d-4e42-88a3-d15ac6d6ee33).
--
--   [Source excerpt, lines 432–445](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L432-L445) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L430-L501 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetProd_of_locally_memLp_two`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Set Filter

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_finsetProd_of_locally_memLp_two_readable {n : ℕ} {ι : Type*}
    [DecidableEq ι] (s : Finset ι)
    {f df : ι → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : EuclideanSpace ℝ (Fin n)}
    (hf : ∀ i ∈ s, HasWeakDerivAlong (f i) (df i) v)
    (hbound : ∀ i ∈ s, MemLp (f i) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : ∀ i ∈ s, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (df i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    HasWeakDerivAlong (fun x => ∏ i ∈ s, f i x)
      (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ i ∈ s, df i x * ∏ j ∈ s.erase i, f j x) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by sorry
