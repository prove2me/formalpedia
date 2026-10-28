-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_norm_sq_le_of_mem_closure_quadratic_bound_readable
-- name    : FunctionalInequalities.KLS.LogConcave.norm_sq_le_of_mem_closure_quadratic_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:50.466993+00:00
-- url     : https://prove2.me/theorems/db1af422-d999-42df-956f-acb4a17024e8
-- title:
--   Quadratic Bound Extends From A Set Closure
-- statement:
--   This is a general Hilbert-space closure lemma.
--
--   Let $H$ be a real inner-product normed space, let $z\in H$, let $S\subseteq H$, and let $C\in\mathbb R$. Assume $z\in\overline S$ and, for every $w\in S$,
--
--   $$
--   2\langle z,w\rangle-\|w\|^2\le C.
--   $$
--
--   Then
--
--   $$
--   \|z\|^2\le C.
--   $$
--
--   The result is reusable for passing variational quadratic inequalities from a dense set to a closure point.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_sq_le_of_mem_closure_quadratic_bound
--       (z : H) {S : Set H} {C : ℝ} (hz : z ∈ closure S)
--       (hbound : ∀ w ∈ S, 2 * ⟪z, w⟫ - ‖w‖ ^ 2 ≤ C) :
--       ‖z‖ ^ 2 ≤ C
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/BrascampLieb`](https://prove2.me/theorems/ef0b3d78-2213-4c3c-ab7c-7dd44bfe1cfb).
--
--   Next: [`inner_center_left_of_mean_zero`](https://prove2.me/theorems/eeca0bb8-9f32-4e5c-ba1e-1f7ba9ea09b0).
--
--   [Source excerpt, lines 42–45](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/BrascampLieb.lean#L42-L45) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/BrascampLieb.lean#L40-L57 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.BrascampLieb`, declaration `FunctionalInequalities.KLS.LogConcave.norm_sq_le_of_mem_closure_quadratic_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_BrascampLieb

open scoped ContDiff RealInnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem FunctionalInequalities.KLS.LogConcave.norm_sq_le_of_mem_closure_quadratic_bound_readable
    (z : H) {S : Set H} {C : ℝ} (hz : z ∈ closure S)
    (hbound : ∀ w ∈ S, 2 * ⟪z, w⟫ - ‖w‖ ^ 2 ≤ C) :
    ‖z‖ ^ 2 ≤ C := by sorry
