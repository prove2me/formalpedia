-- Prove2me | Theorems.Thm_MarkovProcess_FiniteOrderedTimes_translate_translate
-- name    : MarkovProcess.FiniteOrderedTimes.translate_translate
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:09.571585+00:00
-- url     : https://prove2.me/theorems/b7db1614-3809-41e3-9101-66a519a886b9
-- title:
--   MarkovProcess: translate_translate
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

theorem MarkovProcess.FiniteOrderedTimes.translate_translate {n : ℕ} (s r : NNReal) (times : FiniteOrderedTimes n) :
    (times.translate r).translate s = times.translate (s + r) := by sorry
