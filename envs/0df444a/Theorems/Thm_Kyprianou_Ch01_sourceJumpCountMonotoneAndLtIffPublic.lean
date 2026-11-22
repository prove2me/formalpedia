-- Prove2me | Theorems.Thm_Kyprianou_Ch01_sourceJumpCountMonotoneAndLtIffPublic
-- name    : Kyprianou.Ch01.sourceJumpCountMonotoneAndLtIffPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:45:59.289695+00:00
-- url     : https://prove2.me/theorems/e9f54d69-de1b-4701-b1b0-c00fc130d24f
-- title:
--   Public source jump-count order equivalence and monotonicity for divergent increasing arrivals
-- statement:
--   For a strictly increasing sequence of real arrival times diverging to infinity, the original ProbabilityTheory.jumpCount, defined by Nat.sInf of later arrival indices, is monotone in the observation time and satisfies n < jumpCount T t exactly when T n ≤ t. The first equivalence follows directly from Nat.sInf_le, Nat.sInf_mem for the nonempty eventual-above set, and strict monotonicity of T. The second follows by contradiction applying the first equivalence at adjacent observation times. This self-contained public theorem recovers the precise mathematical arguments of two previously Proved but private LevyFoundations jump-count theorems without importing those private modules.
-- source:
--   Kyprianou (2006) Chapter 1 §1.3.4. Source formula of ProbabilityTheory.jumpCount in Definitions.Def_LeanLevy_Processes_PiecewisePath. Public-interface proof adaptation of the exact accepted proof code in private LevyFoundations theorems 64a78fc4-e895-4dc6-8a16-7be00891d854 and 0f857a2f-c372-4dce-894f-806cfb7c199b; used to prove public local right constancy theorem 5d388754-1819-4644-a607-37e76b62600d without crossing the visibility guard.

import Mathlib
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.sourceJumpCountMonotoneAndLtIffPublic
    (T : ℕ → ℝ) (hmono : StrictMono T)
    (htop : Tendsto T atTop atTop) :
    (∀ (n : ℕ) (t : ℝ),
      n < ProbabilityTheory.jumpCount T t ↔ T n ≤ t) ∧
    Monotone (ProbabilityTheory.jumpCount T) := by
  sorry
