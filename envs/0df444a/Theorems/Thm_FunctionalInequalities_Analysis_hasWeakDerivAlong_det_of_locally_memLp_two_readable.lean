-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_det_of_locally_memLp_two_readable
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:37.676815+00:00
-- url     : https://prove2.me/theorems/33254f42-0c89-459e-bcd2-427b387a0099
-- title:
--   Weak Derivative of a Determinant Polynomial
-- statement:
--   Let $A(x)$ be a matrix field indexed by a finite type and let $DA(x)$ be a proposed directional derivative field along a direction $v$. Assume every entry $A_{ij}$ has weak derivative $(DA)_{ij}$ along $v$, every entry of $A$ belongs to $L^{\infty}$, and every entry of $DA$ belongs locally to $L^2$ on compact sets. Then $\det A$ has weak derivative
--
--   $$
--   \partial_v\det A(x)=\sum_{\sigma\in S_I}\operatorname{sgn}(\sigma)
--   \sum_i DA_{\sigma(i),i}(x)
--   \prod_{j\ne i}A_{\sigma(j),j}(x),
--   $$
--
--   and this derivative is locally in $L^2$ on every compact set. No symmetry, positivity, invertibility, or classical differentiability is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasWeakDerivAlong_det_of_locally_memLp_two {d : ℕ} {ι : Type*}
--       [instFintype : Fintype ι] [instDecidableEq : DecidableEq ι]
--       {A DA : EuclideanSpace ℝ (Fin d) → Matrix ι ι ℝ}
--       {v : EuclideanSpace ℝ (Fin d)}
--       (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
--       (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
--         (volume : Measure (EuclideanSpace ℝ (Fin d))))
--       (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
--         MemLp (fun x => DA x i j) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
--       HasWeakDerivAlong (fun x => (A x).det)
--         (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
--           ∑ i : ι, DA x (σ i) i *
--             ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) v ∧
--       ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
--         MemLp (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
--           ∑ i : ι, DA x (σ i) i *
--             ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/WeakDerivative`](https://prove2.me/theorems/3dfbda94-4a39-4ea5-9eac-fd198567c681).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`hasWeakDerivAlong_finsetProd_of_locally_memLp_two`](https://prove2.me/theorems/9810d657-43d4-4de0-a307-1f01259642ca), [`hasWeakDerivAlong_finsetSum_mul`](https://prove2.me/theorems/2618f40b-2846-4d7d-9e77-e6c773de9cee).
--
--   Next: [`hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two`](https://prove2.me/theorems/2e62203f-0ffc-4c8e-8f06-055bcb5ac5d9).
--
--   [Source excerpt, lines 44–62](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L44-L62) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L42-L83 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative

open MeasureTheory Set Filter Matrix

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_det_of_locally_memLp_two_readable {d : ℕ} {ι : Type*}
    [instFintype : Fintype ι] [instDecidableEq : DecidableEq ι]
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix ι ι ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    HasWeakDerivAlong (fun x => (A x).det)
      (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ∑ i : ι, DA x (σ i) i *
          ∏ j ∈ (Finset.univ : Finset ι).erase i, A x (σ j) j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by sorry
