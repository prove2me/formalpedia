-- Prove2me | Theorems.Thm_MarkovProcess_LifetimePath_coordinate_shift_eq_delta_of_lifetime_le
-- name    : MarkovProcess.LifetimePath.coordinate_shift_eq_delta_of_lifetime_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:44.466054+00:00
-- url     : https://prove2.me/theorems/c8894504-3a49-43de-9ef1-383117e99b5d
-- title:
--   MarkovProcess: coordinate_shift_eq_delta_of_lifetime_le
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_Shift_1241ab85
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic time shifts of lifetime paths

This file shifts a lifetime path forward by a fixed finite time. A shift beyond the original
lifetime produces a path with zero lifetime, hence with cemetery state at every coordinate.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovProcess.LifetimePath

noncomputable section

variable {α : Type*} [TopologicalSpace α]

















section Measurable

variable [MeasurableSpace α]



end Measurable

end
end MarkovProcess.LifetimePath


open MarkovProcess
open MarkovProcess.LifetimePath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic time shifts of lifetime paths

This file shifts a lifetime path forward by a fixed finite time. A shift beyond the original
lifetime produces a path with zero lifetime, hence with cemetery state at every coordinate.
-/

open MeasureTheory
open scoped ENNReal



variable {α : Type*} [TopologicalSpace α]













open MarkovProcess.LifetimePath in

theorem MarkovProcess.LifetimePath.coordinate_shift_eq_delta_of_lifetime_le (S t : NNReal) (ω : LifetimePath α)
    (hω : ω.lifetime ≤ (S : ENNReal)) :
    coordinate t (shift S ω) = Cemetery.delta := by sorry
