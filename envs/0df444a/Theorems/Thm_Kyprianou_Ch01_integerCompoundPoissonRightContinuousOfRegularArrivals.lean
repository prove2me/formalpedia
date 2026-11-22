-- Prove2me | Theorems.Thm_Kyprianou_Ch01_integerCompoundPoissonRightContinuousOfRegularArrivals
-- name    : Kyprianou.Ch01.integerCompoundPoissonRightContinuousOfRegularArrivals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:42:44.652822+00:00
-- url     : https://prove2.me/theorems/433a7d12-b4f4-474a-b26a-b3af99bbf888
-- title:
--   Right continuity of the deterministic zero-drift integer compound-Poisson step path
-- statement:
--   For any strictly increasing and divergent real arrival-time sequence T, and any real mark sequence, the integer floor of initial integer population y plus the zero-drift piecewisePath is right-continuous on NNReal at every time. Use the proved local right constancy of jumpCount between a time and the next arrival. On that interval, the source piecewisePath is the finite sum of exactly the same marks and has zero drift, so the floored value is constant; thus the process is eventually equal on the right to the constant process. ContinuousWithinAt follows immediately. This deterministic lemma needs no stochastic assumptions or offspring moments.
-- source:
--   Kyprianou (2006) Ch01 §1.3.4. Deterministic bridge between new jumpCountLocalRightConstOfRegularArrival and original source integerCompoundPoissonRightContinuousAE UUID 89e2d356-663a-425c-afcd-ad3841267c58; source piecewisePath definition in LeanLevy imported via Definitions.Def_LeanLevy_Processes_PiecewisePath.

import Mathlib
import Definitions.Def_LeanLevy_Processes_PiecewisePath
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.integerCompoundPoissonRightContinuousOfRegularArrivals
    (y : ℕ) (T marks : ℕ → ℝ)
    (hmono : StrictMono T) (htop : Tendsto T atTop atTop) :
    ∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun s : ℝ≥0 =>
          Int.floor ((y : ℝ) +
            ProbabilityTheory.piecewisePath 0 0 T marks (s : ℝ)))
        (Set.Ici t) t := by
  sorry
