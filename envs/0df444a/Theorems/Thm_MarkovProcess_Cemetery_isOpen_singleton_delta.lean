-- Prove2me | Theorems.Thm_MarkovProcess_Cemetery_isOpen_singleton_delta
-- name    : MarkovProcess.Cemetery.isOpen_singleton_delta
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:30:37.477839+00:00
-- url     : https://prove2.me/theorems/297ca182-8b53-4c8e-bf61-6da06f8dda4a
-- title:
--   MarkovProcess: isOpen_singleton_delta
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_CemeteryExtension_b0b7bd17
import Definitions.Def_MarkovProcess_V3H_Kernel_Basic_264434f5
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Topology.Constructions.SumProd

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservative cemetery extension of a sub-Markov kernel

This file adjoins an isolated cemetery state to a measurable state space and
extends one sub-Markov kernel to a Markov kernel.  It deliberately makes no
claim about preservation of kernel composition or semigroup laws.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

namespace MarkovProcess

variable {α : Type*}









namespace Kernel

variable [MeasurableSpace α]























end Kernel

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conservative cemetery extension of a sub-Markov kernel

This file adjoins an isolated cemetery state to a measurable state space and
extends one sub-Markov kernel to a Markov kernel.  It deliberately makes no
claim about preservation of kernel composition or semigroup laws.
-/

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal


variable {α : Type*}







open MarkovProcess in

theorem MarkovProcess.Cemetery.isOpen_singleton_delta [TopologicalSpace α] :
    IsOpen ({Cemetery.delta} : Set (Cemetery α)) := by sorry
