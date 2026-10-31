-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_isProbabilityMeasure_finiteSetLaw
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isProbabilityMeasure_finiteSetLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:25.252239+00:00
-- url     : https://prove2.me/theorems/79799cb6-85a5-4abd-a567-6dc40eb93d7c
-- title:
--   MarkovProcess: isProbabilityMeasure_finiteSetLaw
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-set finite-time laws

This file reindexes the ordered finite-time kernels by finite sets of times and proves their
Mathlib-native projectivity. It does not assert or construct a projective-limit measure.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {α : Type*} [MeasurableSpace α]



















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
# Finite-set finite-time laws

This file reindexes the ordered finite-time kernels by finite sets of times and proves their
Mathlib-native projectivity. It does not assert or construct a projective-limit measure.
-/

open MeasureTheory ProbabilityTheory


variable {α : Type*} [MeasurableSpace α]






















open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isProbabilityMeasure_finiteSetLaw (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (I : Finset NNReal) (x : α) :
    IsProbabilityMeasure (finiteSetLaw P I x) := by sorry
