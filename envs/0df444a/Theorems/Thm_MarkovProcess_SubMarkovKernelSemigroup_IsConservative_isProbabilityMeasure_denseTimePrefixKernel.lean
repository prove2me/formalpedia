-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_isProbabilityMeasure_denseTimePrefixKernel
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isProbabilityMeasure_denseTimePrefixKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:24.710817+00:00
-- url     : https://prove2.me/theorems/d5b30d06-5e8b-458b-9fbd-68e89ecb18cc
-- title:
--   MarkovProcess: isProbabilityMeasure_denseTimePrefixKernel
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_PrefixKernel_a192bbea
import Definitions.Def_MarkovProcess_V3H_FiniteTime_ProjectiveFamily_1eff0efa
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
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
# Kernels on finite prefixes of a countable time enumeration

This file constructs the finite-dimensional kernel on the first `n` points of an arbitrary
enumeration, with coordinates retained in enumeration order. The enumeration need not respect
the order of physical time.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

noncomputable section

variable {D α : Type*} [MeasurableSpace α]

















namespace IsConservative







end IsConservative
end
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
# Kernels on finite prefixes of a countable time enumeration

This file constructs the finite-dimensional kernel on the first `n` points of an arbitrary
enumeration, with coordinates retained in enumeration order. The enumeration need not respect
the order of physical time.
-/

open MeasureTheory ProbabilityTheory



variable {D α : Type*} [MeasurableSpace α]




















open MarkovProcess.SubMarkovKernelSemigroup.IsConservative in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.isProbabilityMeasure_denseTimePrefixKernel (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) (x : α) :
    IsProbabilityMeasure (denseTimePrefixKernel P e ι n x) := by sorry
