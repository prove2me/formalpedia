-- Prove2me | Theorems.Thm_MarkovProcess_DenseTimeHistory_historyEquiv_snd_apply
-- name    : MarkovProcess.DenseTimeHistory.historyEquiv_snd_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:31:46.935049+00:00
-- url     : https://prove2.me/theorems/2b7c8f28-f4b0-4639-9ba6-773456ae09e0
-- title:
--   MarkovProcess: historyEquiv_snd_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Time_DenseTimeHistory_28830881
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite dense-time histories

This file provides measurable coordinate equivalences for histories indexed by an initial
segment of the natural numbers. It makes no probability-law, kernel, or stochastic-process claim.
-/

namespace MarkovProcess



namespace DenseTimeHistory

variable {α : Type*} [MeasurableSpace α]



























end DenseTimeHistory

end MarkovProcess


open MarkovProcess
open MarkovProcess.DenseTimeHistory
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite dense-time histories

This file provides measurable coordinate equivalences for histories indexed by an initial
segment of the natural numbers. It makes no probability-law, kernel, or stochastic-process claim.
-/





variable {α : Type*} [MeasurableSpace α]











open MarkovProcess.DenseTimeHistory in
@[simp]

theorem MarkovProcess.DenseTimeHistory.historyEquiv_snd_apply (n : ℕ) (history : DenseTimeHistory α n) (i : Fin n) :
    (historyEquiv n history).2 i = history ⟨i.succ, i.isLt⟩ := by sorry
