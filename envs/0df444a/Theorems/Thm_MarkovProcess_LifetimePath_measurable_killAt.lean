-- Prove2me | Theorems.Thm_MarkovProcess_LifetimePath_measurable_killAt
-- name    : MarkovProcess.LifetimePath.measurable_killAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:47.378515+00:00
-- url     : https://prove2.me/theorems/93aaa806-cca6-4d31-b3ac-8cf41fc5073c
-- title:
--   MarkovProcess: measurable_killAt
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Lifetime_Basic_6f1c513f
import Definitions.Def_MarkovProcess_V3H_Lifetime_Killing_79b59135
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
# Deterministic killing of lifetime paths

This file truncates a lifetime path at a deterministic finite time. The coordinate at the
killing time itself is the cemetery state, so this operation is distinct from endpoint-retaining
stopping.
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
# Deterministic killing of lifetime paths

This file truncates a lifetime path at a deterministic finite time. The coordinate at the
killing time itself is the cemetery state, so this operation is distinct from endpoint-retaining
stopping.
-/

open MeasureTheory
open scoped ENNReal



variable {α : Type*} [TopologicalSpace α]












variable [MeasurableSpace α]

open MarkovProcess.LifetimePath in

theorem MarkovProcess.LifetimePath.measurable_killAt (T : NNReal) :
    Measurable (killAt T : LifetimePath α → LifetimePath α) := by sorry
