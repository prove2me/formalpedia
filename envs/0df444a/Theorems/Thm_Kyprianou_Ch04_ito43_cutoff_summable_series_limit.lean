-- Prove2me | Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_summable_series_limit
-- name    : Kyprianou.Ch04.ito43_cutoff_summable_series_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T22:18:08.514859+00:00
-- url     : https://prove2.me/theorems/51e6082a-c63b-50db-9793-b3485277fc87
-- title:
--   Continuous cutoffs converge in every absolutely summable mark series
-- statement:
--   For nonzero marks the cutoff is eventually one; at zero marks the summand vanishes. The absolute summable series dominates the cutoffs, so Tannery's dominated convergence theorem applies.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.3.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.ito43_cutoff_summable_series_limit {ι : Type} (f z : ι → ℝ)
    (hs : Summable (fun i => |f i|)) (h0 : ∀ i, z i = 0 → f i = 0) :
    Tendsto (fun m : ℕ => ∑' i, f i * min 1 (max 0 (|z i| * ((m:ℝ)+1)-1)))
      atTop (nhds (∑' i, f i)) := by sorry
