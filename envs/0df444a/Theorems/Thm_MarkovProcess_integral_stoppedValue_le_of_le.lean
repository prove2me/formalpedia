-- Prove2me | Theorems.Thm_MarkovProcess_integral_stoppedValue_le_of_le
-- name    : MarkovProcess.integral_stoppedValue_le_of_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:36.409554+00:00
-- url     : https://prove2.me/theorems/1aa40f09-d52b-4ac4-bf96-0f77f126487f
-- title:
--   MarkovProcess: integral_stoppedValue_le_of_le
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_OptionalStopping_4dea182f
import Definitions.Def_MarkovProcess_V3H_Path_StoppingTimeDyadicCeiling_2d75c809
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.Instances.NNReal.Lemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Optional stopping in continuous time, at a bounded finite stopping time

Mathlib's optional stopping theorem is discrete-time.  This file proves the continuous-time
statement the library consumes: if `M` is a real-valued martingale for a filtration indexed by
`ℝ≥0`, bounded on bounded time intervals and right continuous in time along every sample point,
and `T` is a finite stopping time bounded by a deterministic horizon `K`, then

  `∫ omega, M (T omega) omega ∂mu = ∫ omega, M 0 omega ∂mu`

(`integral_stoppedValue_eq_of_locallyBounded`, with the uniformly bounded case
`integral_stoppedValue_eq_of_le`).

For a supermartingale the corresponding expectation is at most its initial expectation
(`integral_stoppedValue_le_of_locallyBounded` and `integral_stoppedValue_le_of_le`).

The proof samples a supermartingale on the dyadic grid and applies Mathlib's
`Submartingale.expected_stoppedValue_mono` after negation.  The dyadic ceilings `T_n` of a finite
stopping time are stopping times with finite range that decrease to `T`
(`Path/StoppingTimeDyadicCeiling.lean`), so dominated convergence and right continuity give the
supermartingale inequality.  Applying that inequality to a martingale and its negation gives the
martingale equality.

Nothing here is specific to path space: the statements are for an arbitrary measurable space with
a filtration indexed by `ℝ≥0`.  No optional-stopping result for unbounded stopping times is
asserted.
-/

open Filter MeasureTheory Topology
open scoped NNReal

namespace MarkovProcess

noncomputable section

variable {Omega : Type*} {m : MeasurableSpace Omega} {mu : Measure Omega}
  {ℱ : Filtration NNReal m} {M : NNReal → Omega → ℝ}

section FiniteRange

variable [IsFiniteMeasure mu]









end FiniteRange

section DyadicApproximation













end DyadicApproximation

section OptionalStopping

variable [IsFiniteMeasure mu]









end OptionalStopping

end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Optional stopping in continuous time, at a bounded finite stopping time

Mathlib's optional stopping theorem is discrete-time.  This file proves the continuous-time
statement the library consumes: if `M` is a real-valued martingale for a filtration indexed by
`ℝ≥0`, bounded on bounded time intervals and right continuous in time along every sample point,
and `T` is a finite stopping time bounded by a deterministic horizon `K`, then

  `∫ omega, M (T omega) omega ∂mu = ∫ omega, M 0 omega ∂mu`

(`integral_stoppedValue_eq_of_locallyBounded`, with the uniformly bounded case
`integral_stoppedValue_eq_of_le`).

For a supermartingale the corresponding expectation is at most its initial expectation
(`integral_stoppedValue_le_of_locallyBounded` and `integral_stoppedValue_le_of_le`).

The proof samples a supermartingale on the dyadic grid and applies Mathlib's
`Submartingale.expected_stoppedValue_mono` after negation.  The dyadic ceilings `T_n` of a finite
stopping time are stopping times with finite range that decrease to `T`
(`Path/StoppingTimeDyadicCeiling.lean`), so dominated convergence and right continuity give the
supermartingale inequality.  Applying that inequality to a martingale and its negation gives the
martingale equality.

Nothing here is specific to path space: the statements are for an arbitrary measurable space with
a filtration indexed by `ℝ≥0`.  No optional-stopping result for unbounded stopping times is
asserted.
-/

open Filter MeasureTheory Topology
open scoped NNReal



variable {Omega : Type*} {m : MeasurableSpace Omega} {mu : Measure Omega}
  {ℱ : Filtration NNReal m} {M : NNReal → Omega → ℝ}




variable [IsFiniteMeasure mu]



open MarkovProcess in

theorem MarkovProcess.integral_stoppedValue_le_of_le (hM : Supermartingale M ℱ mu) {C : ℝ}
    (hC : ∀ (t : NNReal) (omega : Omega), ‖M t omega‖ ≤ C)
    (hright : ∀ (omega : Omega) (v : NNReal),
      ContinuousWithinAt (fun t : NNReal ↦ M t omega) (Set.Ici v) v)
    {T : Omega → NNReal}
    (hT : IsStoppingTime ℱ fun omega ↦ ((T omega : NNReal) : WithTop NNReal))
    {K : NNReal} (hTK : ∀ omega, T omega ≤ K) :
    ∫ omega, M (T omega) omega ∂mu ≤ ∫ omega, M 0 omega ∂mu := by sorry
