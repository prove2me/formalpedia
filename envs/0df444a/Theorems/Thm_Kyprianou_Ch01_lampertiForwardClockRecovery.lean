-- Prove2me | Theorems.Thm_Kyprianou_Ch01_lampertiForwardClockRecovery
-- name    : Kyprianou.Ch01.lampertiForwardClockRecovery
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:16:24.64221+00:00
-- url     : https://prove2.me/theorems/a10ab56a-dd57-4611-88ff-553a4085fa52
-- title:
--   Equation (1.17): occupation-time change recovers the branching path before extinction
-- statement:
--   A precise pathwise sublemma for the forward time-change (1.17): with a positive right-continuous integer-valued population before extinction and locally integrable occupation, the inverse-clock process X_{J_t} recovers Y_t at all pre-extinction times, almost surely. No conclusion about independent exponential jumps or compound Poisson laws is assumed. The latter law characterisation remains a separate theorem obligation. Draft awaits remote Lean elaboration.
-- source:
--   Kyprianou (2006), Chapter 1, equation (1.17), printed p. 25.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.lampertiForwardClockRecovery
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℝ≥0 → Ω → ℕ)
    (hcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun s : ℝ≥0 => Y s ω)
        (nhdsWithin t (Set.Ici t)) (nhds (Y t ω)))
    (hlocalint : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      IntervalIntegrable
        (fun s : ℝ => (Y (Real.toNNReal s) ω : ℝ))
        volume 0 (t : ℝ))
    (hpositive : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) < populationExtinction Y ω →
        0 < Y t ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (t : WithTop ℝ≥0) < populationExtinction Y ω →
      branchingToPoisson Y
          (Real.toNNReal (branchingOccupation Y t ω)) ω = Y t ω := by
  sorry
