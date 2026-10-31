-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_finiteTimeKernel_map_headTail
-- name    : MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel_map_headTail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:30.972913+00:00
-- url     : https://prove2.me/theorems/77cc28f6-58fe-41a4-86df-ffd86f1b6701
-- title:
--   MarkovProcess: finiteTimeKernel_map_headTail
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelConcatenation_cb54f8d1
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.Lemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Concatenating finite-time kernels at an ordered cut

This file factors an ordered finite-dimensional transition law at a designated observation
time.  The future factor is the finite-time kernel at the corresponding relative times, started
from the terminal coordinate of the past.  This is finite-dimensional kernel infrastructure and
does not assert a path-space or conditional Markov theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace MarkovProcess



namespace FiniteOrderedTimes







end FiniteOrderedTimes

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [MeasurableSpace alpha]



































namespace IsConservative






end IsConservative

end SubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Concatenating finite-time kernels at an ordered cut

This file factors an ordered finite-dimensional transition law at a designated observation
time.  The future factor is the finite-time kernel at the corresponding relative times, started
from the terminal coordinate of the past.  This is finite-dimensional kernel infrastructure and
does not assert a path-space or conditional Markov theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory






variable {alpha : Type*} [MeasurableSpace alpha]































open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.finiteTimeKernel_map_headTail (P : SubMarkovKernelSemigroup alpha) {n : ℕ}
    (times : FiniteOrderedTimes (n + 1)) :
    (finiteTimeKernel P times).map
        (fun path ↦ (path 0, Fin.tail path)) =
      P (times 0) ⊗ₖ Kernel.prodMkLeft alpha
        (finiteTimeKernel P times.relativeTail) := by sorry
