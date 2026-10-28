-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translation_scalar_local_bounds_truncation
-- name    : OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_truncation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:15:54.633107+00:00
-- url     : https://prove2.me/theorems/46ef53bf-d184-4200-8dcc-f6d4aa1a6cba
-- title:
--   Positive and weighted truncation bounds
-- statement:
--   Prove each truncation order is positive and its ceiling dominates the corresponding weighted real order. Use `q ≥ 2`, positive `F0` and `v0`, and the defining ceiling inequalities.

import Definitions.Def_OAI_PiExponent_MinorTranslationData
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.MinorTranslationData
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.translation_scalar_local_bounds_truncation
    {nu : ℝ} (d : FixedData nu) :
    (∀ i : Fin d.m,
      1 ≤ MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) ∧
    (∀ i : Fin d.m,
      d.F0 * fixedWeights d i ≤
        (d.v0 : ℝ) *
          MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) := by sorry
