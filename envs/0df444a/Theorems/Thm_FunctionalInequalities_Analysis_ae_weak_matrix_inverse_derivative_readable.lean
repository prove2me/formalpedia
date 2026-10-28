-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_ae_weak_matrix_inverse_derivative_readable
-- name    : FunctionalInequalities.Analysis.ae_weak_matrix_inverse_derivative_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:53.637971+00:00
-- url     : https://prove2.me/theorems/d6fe03d3-18d4-4ee9-8216-cfc3ec407a97
-- title:
--   Almost-Everywhere Derivative Formula for Weak Matrix Inverses
-- statement:
--   This is a technical almost-everywhere inverse differentiation rule for matrix-valued weak derivatives.
--
--   Let $A,R:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(d))\to\mathbb R^{m\times m}$, with weak directional derivatives $DA,DR$ along a fixed direction. Assume:
--
--   1. Every entry of $A$ and $R$ is locally essentially bounded on compact sets (`MemLp` with exponent $\top$).
--   2. Every entry of $DA$ and $DR$ belongs to local $L^2$ on compact sets.
--   3. Almost everywhere, $R(x)A(x)=I$.
--
--   Then, almost everywhere,
--
--   $$DR(x)=-R(x)\,DA(x)\,R(x).$$
--
--   The dimensions $d$ and $m$ are independent and may be zero. The declaration `ae_weak_matrix_inverse_derivative_readable` assumes the weak derivatives and integrability data as inputs; it does not assume classical differentiability.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_weak_matrix_inverse_derivative {d m : ℕ}
--       {A R DA DR : EuclideanSpace ℝ (Fin d) → Matrix (Fin m) (Fin m) ℝ}
--       {v : EuclideanSpace ℝ (Fin d)}
--       (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
--       (hR : ∀ i j, HasWeakDerivAlong (fun x => R x i j) (fun x => DR x i j) v)
--       (hA_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
--         MemLp (fun x => A x i j) (⊤ : ENNReal)
--           ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
--       (hR_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
--         MemLp (fun x => R x i j) (⊤ : ENNReal)
--           ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
--       (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
--         MemLp (fun x => DA x i j) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
--       (hDR2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
--         MemLp (fun x => DR x i j) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
--       (hRA : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), R x * A x = 1) :
--       ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
--         DR x = -(R x * DA x * R x)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/WeakDerivative`](https://prove2.me/theorems/3dfbda94-4a39-4ea5-9eac-fd198567c681).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.congr_ae`](https://prove2.me/theorems/feacd1e3-2d93-4444-8c84-fe52a0849220), [`HasWeakDerivAlong.mul_of_locally_bounded`](https://prove2.me/theorems/1133273b-c737-4c38-bf2a-2953cd23a941), [`hasWeakDerivAlong_finsetSum_mul`](https://prove2.me/theorems/2618f40b-2846-4d7d-9e77-e6c773de9cee), [`hasWeakDerivAlong_of_contDiff`](https://prove2.me/theorems/4e2a811d-5127-4a66-87f8-6417e73ed552).
--
--   Previous: [`hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two`](https://prove2.me/theorems/2e62203f-0ffc-4c8e-8f06-055bcb5ac5d9) · Next: [`bounded_trace_quadratic_weak_derivative_data`](https://prove2.me/theorems/cc2fdc63-2222-4fdb-85c7-4532eb76bc0c).
--
--   [Source excerpt, lines 130–149](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L130-L149) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L128-L198 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, declaration `FunctionalInequalities.Analysis.ae_weak_matrix_inverse_derivative`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative

open MeasureTheory Set Matrix

theorem FunctionalInequalities.Analysis.ae_weak_matrix_inverse_derivative_readable {d m : ℕ}
    {A R DA DR : EuclideanSpace ℝ (Fin d) → Matrix (Fin m) (Fin m) ℝ}
    {v : EuclideanSpace ℝ (Fin d)}
    (hA : ∀ i j, HasWeakDerivAlong (fun x => A x i j) (fun x => DA x i j) v)
    (hR : ∀ i j, HasWeakDerivAlong (fun x => R x i j) (fun x => DR x i j) v)
    (hA_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => A x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hR_top : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => R x i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hDA2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hDR2 : ∀ i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DR x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S))
    (hRA : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), R x * A x = 1) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      DR x = -(R x * DA x * R x) := by sorry
