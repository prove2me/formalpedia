-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_bounded_trace_quadratic_weak_derivative_data_readable
-- name    : FunctionalInequalities.Analysis.bounded_trace_quadratic_weak_derivative_data_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:43.571617+00:00
-- url     : https://prove2.me/theorems/cc2fdc63-2222-4fdb-85c7-4532eb76bc0c
-- title:
--   Bounded Trace Quadratic Derivative Data
-- statement:
--   This packages boundedness, local integrability, and weak derivative data for a trace quadratic.
--
--   Let $d,n\in\mathbb N$, let $B\in M_n(\mathbb R)$, let $A:\mathbb R^d\to M_n(\mathbb R)$, let $DA:\mathbb R^d\to M_n(\mathbb R)$ be indexed by coordinate directions, and let $M\in[0,\infty)$ be represented by an `NNReal`. Assume:
--
--   1. Every entry of $A$ is measurable.
--   2. For all $x,i,j$, $\|A_{ij}(x)\|\le M$.
--   3. Each entry of $A$ has the stated weak derivative $DA_k$ in the coordinate direction given by `EuclideanSpace.basisFun`.
--   4. Every entry of each $DA_k$ belongs to $L^2$ on every compact restriction of volume measure.
--
--   Then there exists $C\ge0$ such that
--
--   $$
--   \|\operatorname{tr}(BA(x)BA(x))\|\le C
--   $$
--
--   for every $x$, the trace quadratic is locally integrable, and for every coordinate $k$ its weak derivative is
--
--   $$
--   2\,\operatorname{tr}(BA(x)B\,DA_k(x)),
--   $$
--
--   with this derivative in $L^2$ on every compact set. The declaration is `bounded_trace_quadratic_weak_derivative_data_readable`; all finite ambient and matrix dimensions, including zero dimensions, are permitted.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem bounded_trace_quadratic_weak_derivative_data {d n : ℕ}
--       (B : Matrix (Fin n) (Fin n) ℝ)
--       (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
--       (DA : Fin d → EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
--       {M : NNReal}
--       (hmeas : ∀ i j, Measurable (fun x => A x i j))
--       (hbound : ∀ x i j, ‖A x i j‖ ≤ (M : ℝ))
--       (hweak : ∀ k i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA k x i j)
--         (EuclideanSpace.basisFun (Fin d) ℝ k))
--       (hDA2 : ∀ k i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
--         MemLp (fun x => DA k x i j) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
--       ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖(B * A x * B * A x).trace‖ ≤ C) ∧
--         LocallyIntegrable (fun x => (B * A x * B * A x).trace)
--           (volume : Measure (EuclideanSpace ℝ (Fin d))) ∧
--         ∀ k : Fin d,
--           HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
--             (fun x => 2 * (B * A x * B * DA k x).trace)
--             (EuclideanSpace.basisFun (Fin d) ℝ k) ∧
--           ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
--             MemLp (fun x => 2 * (B * A x * B * DA k x).trace) 2
--               ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/WeakDerivative`](https://prove2.me/theorems/3dfbda94-4a39-4ea5-9eac-fd198567c681).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two`](https://prove2.me/theorems/2e62203f-0ffc-4c8e-8f06-055bcb5ac5d9), [`trace_mul_mul_mul_eq_sum`](https://prove2.me/theorems/341ba53c-b3cb-4ad0-873d-9d84885a6c75).
--
--   Previous: [`ae_weak_matrix_inverse_derivative`](https://prove2.me/theorems/d6fe03d3-18d4-4ee9-8216-cfc3ec407a97) · Next: [`bounded_weak_matrix_product_entry`](https://prove2.me/theorems/3c19e2fb-eb53-4358-81de-489fd6539c03).
--
--   [Source excerpt, lines 212–233](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L212-L233) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L209-L263 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, declaration `FunctionalInequalities.Analysis.bounded_trace_quadratic_weak_derivative_data`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative

open MeasureTheory Set Filter Matrix

theorem FunctionalInequalities.Analysis.bounded_trace_quadratic_weak_derivative_data_readable {d n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    (DA : Fin d → EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    {M : NNReal}
    (hmeas : ∀ i j, Measurable (fun x => A x i j))
    (hbound : ∀ x i j, ‖A x i j‖ ≤ (M : ℝ))
    (hweak : ∀ k i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA k x i j)
      (EuclideanSpace.basisFun (Fin d) ℝ k))
    (hDA2 : ∀ k i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA k x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖(B * A x * B * A x).trace‖ ≤ C) ∧
      LocallyIntegrable (fun x => (B * A x * B * A x).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin d))) ∧
      ∀ k : Fin d,
        HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
          (fun x => 2 * (B * A x * B * DA k x).trace)
          (EuclideanSpace.basisFun (Fin d) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
          MemLp (fun x => 2 * (B * A x * B * DA k x).trace) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by sorry
