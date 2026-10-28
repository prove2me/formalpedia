-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_inner_self_pos_of_norm_sub_one_lt_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.inner_self_pos_of_norm_sub_one_lt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:49.351884+00:00
-- url     : https://prove2.me/theorems/3500b35b-5a79-4cfe-8a40-9807fb6246e9
-- title:
--   Strict Positivity Near the Identity
-- statement:
--   This is an operator positivity estimate.
--
--   Let $E$ be a complete real inner-product normed space, let $A:E\to E$ be continuous linear, and assume
--   $\|A-I\|<1$. For every nonzero vector $v\in E$,
--
--   $$
--   0<\langle Av,v\rangle.
--   $$
--
--   Thus an operator lying within operator norm $1$ of the identity has a strictly positive quadratic form. The theorem is a technical criterion used to obtain invertibility from norm convergence; self-adjointness is not an explicit hypothesis in the type.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem inner_self_pos_of_norm_sub_one_lt
--       [CompleteSpace E]
--       {A : E →L[ℝ] E} (hA : ‖A - 1‖ < 1) {v : E} (hv : v ≠ 0) :
--       0 < ⟪A v, v⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Previous: [`opNorm_le_of_inner_eq`](https://prove2.me/theorems/1886b5dc-8b60-448e-812c-d2f3b3c38710) · Next: [`exists_standardized`](https://prove2.me/theorems/b86ffa3f-dfc6-43a2-8cd2-8a6a6fc5a590).
--
--   [Source excerpt, lines 166–169](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L166-L169) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L165-L181 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CompactReduction`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.inner_self_pos_of_norm_sub_one_lt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.KLS.LogConcave.Suspension.inner_self_pos_of_norm_sub_one_lt_readable
    [CompleteSpace E]
    {A : E →L[ℝ] E} (hA : ‖A - 1‖ < 1) {v : E} (hv : v ≠ 0) :
    0 < ⟪A v, v⟫ := by sorry
