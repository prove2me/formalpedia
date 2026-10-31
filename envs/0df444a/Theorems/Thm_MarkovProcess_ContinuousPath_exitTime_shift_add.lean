-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_exitTime_shift_add
-- name    : MarkovProcess.ContinuousPath.exitTime_shift_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:04.442967+00:00
-- url     : https://prove2.me/theorems/0ee4d7c8-39b6-4a60-97ac-0b909d7ce975
-- title:
--   MarkovProcess: exitTime_shift_add
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_ExitTimeShift_63f55a50
import Definitions.Def_MarkovProcess_V3H_Path_ExitTime_92962b9e
import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times under shifts

Path-space identities relating the exit time `ContinuousPath.exitTime U` of an open set to the
shift `ContinuousPath.shift t`, and the measurability of the survival events they generate.

* `exitTime_shift_add`: before the exit time, shifting by `t` subtracts `t` from the exit time,
  `τ(θ_t ω) + t = τ(ω)` whenever `t < τ(ω)`;
* `coe_add_lt_exitTime_iff`: the event identity `{t + s < τ} = {t < τ} ∩ {s < τ ∘ θ_t}`, which is
  the Chapman--Kolmogorov identity for the process killed at `τ`;
* `measurableSet_lt_exitTime_canonicalFiltration`, `measurableSet_lt_exitTime`,
  `measurable_exitTime`: the survival event `{t < τ}` is measurable for the canonical filtration
  at time `t`, and the exit time is a Borel function on path space.

Nothing here involves a probability law.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MarkovProcess.ContinuousPath

section Shift

variable {alpha : Type*} [PseudoMetricSpace alpha]







end Shift

section Measurable

variable {alpha : Type*} [PseudoMetricSpace alpha] [MeasurableSpace alpha] [BorelSpace alpha]







end Measurable

end MarkovProcess.ContinuousPath


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exit times under shifts

Path-space identities relating the exit time `ContinuousPath.exitTime U` of an open set to the
shift `ContinuousPath.shift t`, and the measurability of the survival events they generate.

* `exitTime_shift_add`: before the exit time, shifting by `t` subtracts `t` from the exit time,
  `τ(θ_t ω) + t = τ(ω)` whenever `t < τ(ω)`;
* `coe_add_lt_exitTime_iff`: the event identity `{t + s < τ} = {t < τ} ∩ {s < τ ∘ θ_t}`, which is
  the Chapman--Kolmogorov identity for the process killed at `τ`;
* `measurableSet_lt_exitTime_canonicalFiltration`, `measurableSet_lt_exitTime`,
  `measurable_exitTime`: the survival event `{t < τ}` is measurable for the canonical filtration
  at time `t`, and the exit time is a Borel function on path space.

Nothing here involves a probability law.
-/

open MeasureTheory Set
open scoped ENNReal NNReal



variable {alpha : Type*} [PseudoMetricSpace alpha]



open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.exitTime_shift_add (U : Set alpha) (omega : ContinuousPath alpha) (t : NNReal)
    (ht : (t : ℝ≥0∞) < exitTime U omega) :
    exitTime U (shift t omega) + t = exitTime U omega := by sorry
