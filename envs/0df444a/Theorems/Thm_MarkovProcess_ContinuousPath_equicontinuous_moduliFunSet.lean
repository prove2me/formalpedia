-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_equicontinuous_moduliFunSet
-- name    : MarkovProcess.ContinuousPath.equicontinuous_moduliFunSet
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:02.923098+00:00
-- url     : https://prove2.me/theorems/e7047e1f-ea65-4ed5-932a-08eeeca6a1f1
-- title:
--   MarkovProcess: equicontinuous_moduliFunSet
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_PathModulus_4f3af818
import Definitions.Def_MarkovProcess_V3H_Continuity_PathTightness_ad16da33
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.UniformSpace.Ascoli

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact sets of paths, and tightness on continuous-path space

A family of laws on `C([0, ∞), alpha)` is tight as soon as two things hold uniformly over the
family: the time-zero position lies in a fixed compact set, and the oscillation over each bounded
time interval is controlled at a scale that does not depend on the law.  This file supplies the
compact sets that make that statement work and then assembles the tightness estimate.

The compact sets are `ContinuousPath.moduliSet K0 delta r`: the paths starting in `K0` whose
oscillation over `[0, n]` at scale `delta n` is at most `r n`, for every natural `n`.  When
`r n → 0` these conditions are exactly equicontinuity, so Arzelà--Ascoli applies as soon as the
values of the family at each fixed time stay in a compact set.  That last requirement --- the
compact containment condition of the weak-convergence literature --- is isolated as a hypothesis
in `isCompact_moduliSet_of_forall_isCompact`; over a *proper* metric state space (closed balls
compact) it is automatic, because the modulus already confines a path to a bounded neighbourhood
of its starting point, and `isCompact_moduliSet` discharges it.

Main results:

* `MarkovProcess.ContinuousPath.edist_le_of_modulus`, the chaining bound from the starting point;
* `MarkovProcess.ContinuousPath.moduliSet` and `moduliFunSet`, with closedness and
  equicontinuity;
* `MarkovProcess.ContinuousPath.isCompact_moduliSet_of_forall_isCompact` and
  `isCompact_moduliSet`, the Arzelà--Ascoli compactness statements;
* `MarkovProcess.ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le`, tightness of a
  family of laws from a uniform modulus estimate and a compact time-zero law.

Nothing here constructs a law, and no compactness theorem for measures (Prokhorov's theorem) is
proved or used.
-/

open Filter MeasureTheory Metric Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace ContinuousPath

variable {alpha : Type*} [MetricSpace alpha]

section Chaining



end Chaining

section Moduli















end Moduli

section Tight





end Tight

end ContinuousPath

end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Compact sets of paths, and tightness on continuous-path space

A family of laws on `C([0, ∞), alpha)` is tight as soon as two things hold uniformly over the
family: the time-zero position lies in a fixed compact set, and the oscillation over each bounded
time interval is controlled at a scale that does not depend on the law.  This file supplies the
compact sets that make that statement work and then assembles the tightness estimate.

The compact sets are `ContinuousPath.moduliSet K0 delta r`: the paths starting in `K0` whose
oscillation over `[0, n]` at scale `delta n` is at most `r n`, for every natural `n`.  When
`r n → 0` these conditions are exactly equicontinuity, so Arzelà--Ascoli applies as soon as the
values of the family at each fixed time stay in a compact set.  That last requirement --- the
compact containment condition of the weak-convergence literature --- is isolated as a hypothesis
in `isCompact_moduliSet_of_forall_isCompact`; over a *proper* metric state space (closed balls
compact) it is automatic, because the modulus already confines a path to a bounded neighbourhood
of its starting point, and `isCompact_moduliSet` discharges it.

Main results:

* `MarkovProcess.ContinuousPath.edist_le_of_modulus`, the chaining bound from the starting point;
* `MarkovProcess.ContinuousPath.moduliSet` and `moduliFunSet`, with closedness and
  equicontinuity;
* `MarkovProcess.ContinuousPath.isCompact_moduliSet_of_forall_isCompact` and
  `isCompact_moduliSet`, the Arzelà--Ascoli compactness statements;
* `MarkovProcess.ContinuousPath.isTightMeasureSet_of_measure_compl_modulusSet_le`, tightness of a
  family of laws from a uniform modulus estimate and a compact time-zero law.

Nothing here constructs a law, and no compactness theorem for measures (Prokhorov's theorem) is
proved or used.
-/

open Filter MeasureTheory Metric Topology
open scoped ENNReal NNReal



variable {alpha : Type*} [MetricSpace alpha]









open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.equicontinuous_moduliFunSet {K0 : Set alpha} {delta rho : ℕ → ℝ≥0∞}
    (hdelta : ∀ n, 0 < delta n) (hrho : Tendsto rho atTop (nhds 0)) :
    Equicontinuous fun f : moduliFunSet K0 delta rho ↦ (f : ℝ≥0 → alpha) := by sorry
