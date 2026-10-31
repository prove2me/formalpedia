-- Prove2me | Theorems.Thm_MarkovProcess_LifetimePath_measurable_shift
-- name    : MarkovProcess.LifetimePath.measurable_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:47.961329+00:00
-- url     : https://prove2.me/theorems/4a17a325-4148-48fc-8608-dad3642e8260
-- title:
--   MarkovProcess: measurable_shift
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


















variable [MeasurableSpace α]

open MarkovProcess.LifetimePath in

theorem MarkovProcess.LifetimePath.measurable_shift (S : NNReal) :
    Measurable (shift S : LifetimePath α → LifetimePath α) := by sorry
