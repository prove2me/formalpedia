-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvFiniteAffineSumAbsBoundV1
-- name    : Kyprianou.Ch04.bvFiniteAffineSumAbsBoundV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:31:29.782295+00:00
-- url     : https://prove2.me/theorems/a50f3224-3848-4c45-9004-a6b212f941d7
-- title:
--   Common compact bound for absolutely summable finite affine sums
-- statement:
--   Triangle inequality, absolute summability and the bound on the time coordinate give a common radius for every finite subset and either time indicator.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; compact deterministic estimates.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvFiniteAffineSumAbsBoundV1
    {I : Type} (g : I → ℝ) (hg : Summable (fun i => |g i|))
    (a c u T : ℝ) (hu : 0 ≤ u) (ht : u ≤ T)
    (p : I → Prop) [DecidablePred p] (S : Finset I) :
    |a + c * u + ∑ i ∈ S, if p i then g i else 0| ≤
      |a| + |c| * T + ∑' i, |g i| := by
  sorry
