-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_norm_sub_one_le_of_isPositive_mul_self_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.norm_sub_one_le_of_isPositive_mul_self_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:45.078285+00:00
-- url     : https://prove2.me/theorems/eb4c41c1-de2e-4b9b-953d-d2442f523791
-- title:
--   Positive Square Root Norm Estimate
-- statement:
--   This is a technical estimate for positive continuous linear operators.
--
--   Let $E$ be a complete real inner-product normed space, and let $S,Q:E\to E$ be continuous linear maps. Assume that $S$ is positive and that
--   $S^2=Q$, where multiplication denotes composition. Then
--
--   $$
--   \|S-I\|\le\|Q-I\|.
--   $$
--
--   The result records that a positive square root is no farther from the identity, in operator norm, than its square. It is used in covariance-whitening and approximation arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem norm_sub_one_le_of_isPositive_mul_self
--       [CompleteSpace E]
--       {S Q : E →L[ℝ] E} (hS : S.IsPositive)
--       (hQ : S * S = Q) : ‖S - 1‖ ≤ ‖Q - 1‖
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Previous: [`cumulantBoundCompact_two_of_letwinCompact`](https://prove2.me/theorems/5e9f20a0-75af-4b56-97f4-5f51be0ce81a) · Next: [`opNorm_le_of_inner_eq`](https://prove2.me/theorems/1886b5dc-8b60-448e-812c-d2f3b3c38710).
--
--   [Source excerpt, lines 115–118](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L115-L118) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L114-L143 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CompactReduction`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.norm_sub_one_le_of_isPositive_mul_self`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.KLS.LogConcave.Suspension.norm_sub_one_le_of_isPositive_mul_self_readable
    [CompleteSpace E]
    {S Q : E →L[ℝ] E} (hS : S.IsPositive)
    (hQ : S * S = Q) : ‖S - 1‖ ≤ ‖Q - 1‖ := by sorry
