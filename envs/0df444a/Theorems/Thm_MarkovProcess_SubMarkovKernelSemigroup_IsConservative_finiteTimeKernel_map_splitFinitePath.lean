-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_finiteTimeKernel_map_splitFinitePath
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_splitFinitePath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:17.554026+00:00
-- url     : https://prove2.me/theorems/f4756dad-f321-40b4-a96b-3619fc2d9b36
-- title:
--   MarkovProcess: finiteTimeKernel_map_splitFinitePath
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
open MarkovProcess.SubMarkovKernelSemigroup.IsConservative
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






































open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.finiteTimeKernel_map_splitFinitePath
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (m n : ℕ) (times : FiniteOrderedTimes (n + (m + 1))) :
    (finiteTimeKernel P times).map
        (splitFinitePath (alpha := alpha) (m := m) (n := n)) =
      finiteTimeKernel P (FiniteOrderedTimes.initialSegment times) ⊗ₖ
        (finiteTimeKernel P (FiniteOrderedTimes.relativeFinalSegment times)).comap
          (splitPastTerminal (alpha := alpha) (m := m))
          measurable_splitPastTerminal := by sorry
