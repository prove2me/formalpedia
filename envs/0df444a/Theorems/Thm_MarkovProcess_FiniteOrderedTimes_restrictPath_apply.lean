-- Prove2me | Theorems.Thm_MarkovProcess_FiniteOrderedTimes_restrictPath_apply
-- name    : MarkovProcess.FiniteOrderedTimes.restrictPath_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:04.650455+00:00
-- url     : https://prove2.me/theorems/5dbdf02c-5b5f-4f82-8ea7-202245bc50ce
-- title:
--   MarkovProcess: restrictPath_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Time_FiniteOrderedTimes_717796dd
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/

namespace MarkovProcess



namespace FiniteOrderedTimes









































end FiniteOrderedTimes

end MarkovProcess


open MarkovProcess
open MarkovProcess.FiniteOrderedTimes
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite ordered time families

This file provides increasing finite families of nonnegative times and the elementary operations
for restricting such families and their coordinate paths along order embeddings.  It is an
ordinary finite-dimensional API and makes no probability-law or stochastic-process claim.
-/































open MarkovProcess.FiniteOrderedTimes in
@[simp]

theorem MarkovProcess.FiniteOrderedTimes.restrictPath_apply {m n : ℕ} (e : Fin m ↪o Fin n) {α : Type*}
    (path : Fin n → α) (i : Fin m) : restrictPath e path i = path (e i) := by sorry
