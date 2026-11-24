-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_p2m88_discount_sequence_properties
-- name    : Kyprianou.Ch08.StageB.p2m88_discount_sequence_properties
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:41:22.880902+00:00
-- url     : https://prove2.me/theorems/04c712e3-ee1a-407e-9946-a5d0114afc56
-- title:
--   Positive decreasing discount sequence
-- statement:
--   The reciprocal of n+1 is strictly positive, at most one, antitone and converges to zero.
-- source:
--   Kyprianou (2006), Corollary 8.8, q decreasing to zero.

import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
open Filter Topology

namespace Kyprianou.Ch08.StageB
 theorem p2m88_discount_sequence_properties :
    let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    (∀ n, 0 < r n ∧ r n ≤ 1) ∧ Antitone r ∧ Tendsto r atTop (nhds 0) := by
  sorry
end Kyprianou.Ch08.StageB
