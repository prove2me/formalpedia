-- Prove2me | Theorems.Thm_MarkovProcess_FiniteOrderedTimes_restrictPath_empty
-- name    : MarkovProcess.FiniteOrderedTimes.restrictPath_empty
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:07.004779+00:00
-- url     : https://prove2.me/theorems/ca2ee858-2ec2-4405-b973-ca97e02dd9e2
-- title:
--   MarkovProcess: restrictPath_empty
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

theorem MarkovProcess.FiniteOrderedTimes.restrictPath_empty {n : ℕ} (e : Fin 0 ↪o Fin n) {α : Type*}
    (path : Fin n → α) : restrictPath e path = emptyPath α := by sorry
