-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_bounded_weak_matrix_product_entry_readable
-- name    : FunctionalInequalities.Analysis.bounded_weak_matrix_product_entry_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:52.887249+00:00
-- url     : https://prove2.me/theorems/3c19e2fb-eb53-4358-81de-489fd6539c03
-- title:
--   Weak Derivatives of a Two-Sided Matrix Product
-- statement:
--   This gives boundedness and weak derivative data for entries of a constant two-sided matrix product.
--
--   Let $d,n\in\mathbb N$, let $S\in M_n(\mathbb R)$ be constant, let $H,DH:\mathbb R^d\to M_n(\mathbb R)$, let $v\in\mathbb R^d$, and let $M\in\mathbb R$. Assume every entry of $H$ has weak derivative given by the corresponding entry of $DH$ in direction $v$, every entry satisfies $\|H_{ab}(x)\|\le M$, and every entry of $DH$ is in $L^2$ on every compact restriction of volume measure.
--
--   For every $i,j\in\operatorname{Fin}(n)$, the entry of $SH(x)S$ satisfies
--
--   $$
--   \|(SH(x)S)_{ij}\|\le\sum_{a,b}\|S_{ia}S_{bj}\|\max(M,0),
--   $$
--
--   has weak derivative $(SDH(x)S)_{ij}$ in direction $v$, and that derivative belongs to $L^2$ on every compact set. The declaration is `bounded_weak_matrix_product_entry_readable` and has no positivity, invertibility, or nonzero-dimension assumptions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem bounded_weak_matrix_product_entry {d n : ℕ}
--       (S : Matrix (Fin n) (Fin n) ℝ)
--       {H DH : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ}
--       {v : EuclideanSpace ℝ (Fin d)} (M : ℝ)
--       (hH : ∀ a b, HasWeakDerivAlong (fun x => H x a b) (fun x => DH x a b) v)
--       (hbound : ∀ x a b, ‖H x a b‖ ≤ M)
--       (hD : ∀ a b, ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
--         MemLp (fun x => DH x a b) 2 ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K))
--       (i j : Fin n) :
--       (∀ x, ‖(S * H x * S) i j‖ ≤
--         ∑ q : Fin n × Fin n, ‖S i q.1 * S q.2 j‖ * max M 0) ∧
--       HasWeakDerivAlong (fun x => (S * H x * S) i j) (fun x => (S * DH x * S) i j) v ∧
--       ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
--         MemLp (fun x => (S * DH x * S) i j) 2
--           ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/WeakDerivative`](https://prove2.me/theorems/3dfbda94-4a39-4ea5-9eac-fd198567c681).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`hasWeakDerivAlong_finsetSum_mul`](https://prove2.me/theorems/2618f40b-2846-4d7d-9e77-e6c773de9cee).
--
--   Previous: [`bounded_trace_quadratic_weak_derivative_data`](https://prove2.me/theorems/cc2fdc63-2222-4fdb-85c7-4532eb76bc0c).
--
--   [Source excerpt, lines 290–304](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L290-L304) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean#L286-L321 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakDerivative`, declaration `FunctionalInequalities.Analysis.bounded_weak_matrix_product_entry`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative

open MeasureTheory Matrix
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.Analysis.bounded_weak_matrix_product_entry_readable {d n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ)
    {H DH : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ}
    {v : EuclideanSpace ℝ (Fin d)} (M : ℝ)
    (hH : ∀ a b, HasWeakDerivAlong (fun x => H x a b) (fun x => DH x a b) v)
    (hbound : ∀ x a b, ‖H x a b‖ ≤ M)
    (hD : ∀ a b, ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
      MemLp (fun x => DH x a b) 2 ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K))
    (i j : Fin n) :
    (∀ x, ‖(S * H x * S) i j‖ ≤
      ∑ q : Fin n × Fin n, ‖S i q.1 * S q.2 j‖ * max M 0) ∧
    HasWeakDerivAlong (fun x => (S * H x * S) i j) (fun x => (S * DH x * S) i j) v ∧
    ∀ K : Set (EuclideanSpace ℝ (Fin d)), IsCompact K →
      MemLp (fun x => (S * DH x * S) i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict K) := by sorry
