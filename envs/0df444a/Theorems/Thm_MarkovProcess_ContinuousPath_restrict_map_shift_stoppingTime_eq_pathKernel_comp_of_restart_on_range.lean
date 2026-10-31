-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
-- name    : MarkovProcess.ContinuousPath.restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:16.152463+00:00
-- url     : https://prove2.me/theorems/beaf4d95-d0f6-4406-80aa-36ddd6f21da4
-- title:
--   MarkovProcess: restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_RandomShiftMeasurability_fbe17c52
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Measure-level restart at countable-range stopping times

Deterministic-time restricted restart identities at the attained times of a countable-range
finite stopping time patch to the measure-level identity at that stopping time: restricting the
path law to an event in the stopped sigma-algebra and shifting by the stopping time gives the
path kernel restarted from the state at the stopping time.  The proof decomposes the event over
the countable level sets of the stopping time.

This is ordinary conditional infrastructure.  The restart hypothesis is an assumption here; it
is proved for the continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]



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
# Measure-level restart at countable-range stopping times

Deterministic-time restricted restart identities at the attained times of a countable-range
finite stopping time patch to the measure-level identity at that stopping time: restricting the
path law to an event in the stopped sigma-algebra and shifting by the stopping time gives the
path kernel restarted from the state at the stopping time.  The proof decomposes the event over
the countable level sets of the stopping time.

This is ordinary conditional infrastructure.  The restart hypothesis is an assumption here; it
is proved for the continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal


variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]

open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.restrict_map_shift_stoppingTime_eq_pathKernel_comp_of_restart_on_range
    (Q : Kernel alpha (ContinuousPath alpha))
    (x : alpha) (tau : ContinuousPath alpha → NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (tau omega : WithTop NNReal)))
    (htauRange : (Set.range tau).Countable)
    (hRestart : ∀ S ∈ Set.range tau, ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[canonicalFiltration (alpha := alpha) S] A →
        ((Q x).restrict A).map (shift S) =
          Kernel.comap Q (coordinateProcess (alpha := alpha) S)
              (measurable_coordinateProcess S) ∘ₘ ((Q x).restrict A)) :
    ∀ A : Set (ContinuousPath alpha), MeasurableSet[htau.measurableSpace] A →
      ((Q x).restrict A).map (fun omega ↦ shift (tau omega) omega) =
        Kernel.comap Q (fun omega ↦ omega (tau omega))
            (measurable_eval_stoppingTime_borel tau htau) ∘ₘ ((Q x).restrict A) := by sorry
