-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_readable
-- name    : FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:48.956328+00:00
-- url     : https://prove2.me/theorems/2e62203f-0ffc-4c8e-8f06-055bcb5ac5d9
-- title:
--   Weak Derivative of a Trace Quadratic
-- statement:
--   This formalizes the weak differentiation rule for a trace quadratic with locally square-integrable derivative data.
--
--   Let $d,n\in\mathbb N$, let $B\in M_n(\mathbb R)$ be constant, let $A,DA:\mathbb R^d\to M_n(\mathbb R)$, and let $v\in\mathbb R^d$. Assume:
--
--   1. Every entry $A_{ij}$ has weak derivative $(DA)_{ij}$ in direction $v$.
--   2. Every entry of $A$ belongs to $L^\infty$ with respect to volume measure.
--   3. For every compact set $S\subseteq\mathbb R^d$, every entry of $DA$ belongs to $L^2(S)$.
--
--   Then the function $x\mapsto\operatorname{tr}(BA(x)BA(x))$ has weak derivative in direction $v$ given by
--
--   $$
--   2\,\operatorname{tr}(BA(x)B\,DA(x)),
--   $$
--
--   and this derivative belongs to $L^2(S)$ for every compact $S$. The Lean declaration is `hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_readable`. It is a technical polynomial chain rule; zero dimensions and arbitrary real constant matrices are allowed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two {d n : ℕ}
--       (B : Matrix (Fin n) (Fin n) ℝ)
--       {A DA : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ}
--       {v : EuclideanSpace ℝ (Fin d)}
--       (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
--       (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
--         (volume : Measure (EuclideanSpace ℝ (Fin d))))
--       (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
--         MemLp (fun x => DA x i j) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
--       HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
--         (fun x => 2 * (B * A x * B * DA x).trace) v ∧
--       ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
--         MemLp (fun x => 2 * (B * A x * B * DA x).trace) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/WeakDerivative`](https://prove2.me/theorems/3dfbda94-4a39-4ea5-9eac-fd198567c681).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.mul_of_locally_memLp_two`](https://prove2.me/theorems/4c31865f-283b-4c42-8cee-41884d14d427), [`hasWeakDerivAlong_finsetSum_mul`](https://prove2.me/theorems/2618f40b-2846-4d7d-9e77-e6c773de9cee), [`trace_mul_mul_mul_eq_sum`](https://prove2.me/theorems/341ba53c-b3cb-4ad0-873d-9d84885a6c75).
--
--   Previous: [`hasWeakDerivAlong_det_of_locally_memLp_two`](https://prove2.me/theorems/33254f42-0c89-459e-bcd2-427b387a0099) · Next: [`ae_weak_matrix_inverse_derivative`](https://prove2.me/theorems/d6fe03d3-18d4-4ee9-8216-cfc3ec407a97).
--
--   [Source excerpt, lines 87–101](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L87-L101) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L85-L117 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, declaration `FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative

open MeasureTheory Set Filter Matrix

theorem FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_readable {d n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    {A DA : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hbound : ∀ i j, MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
      (fun x => 2 * (B * A x * B * DA x).trace) v ∧
    ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => 2 * (B * A x * B * DA x).trace) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by sorry
