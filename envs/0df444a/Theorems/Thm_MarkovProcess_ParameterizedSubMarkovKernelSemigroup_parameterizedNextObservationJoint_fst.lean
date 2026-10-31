-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_parameterizedNextObservationJoint_fst
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedNextObservationJoint_fst
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:27.115027+00:00
-- url     : https://prove2.me/theorems/fc02dba4-a183-4ce3-8ca3-3b3ed2abb7c6
-- title:
--   MarkovProcess: parameterizedNextObservationJoint_fst
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimeConditionalKernel_90321c52
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimePrefixKernel_12387c59
import Definitions.Def_MarkovProcess_V3H_Time_DenseTimeHistory_28830881
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
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional kernels for parameterized finite dense-time prefixes

This file disintegrates the jointly parameterized law of a finite dense-time prefix and its next
observation. The resulting conditional kernel is one jointly measurable version. No comparison
with separately chosen fixed-parameter conditional versions is asserted.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]



variable [StandardBorelSpace alpha] [Nonempty alpha]









end
end ParameterizedSubMarkovKernelSemigroup
end MarkovProcess


open MarkovProcess
open MarkovProcess.ParameterizedSubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional kernels for parameterized finite dense-time prefixes

This file disintegrates the jointly parameterized law of a finite dense-time prefix and its next
observation. The resulting conditional kernel is one jointly measurable version. No comparison
with separately chosen fixed-parameter conditional versions is asserted.
-/

open MeasureTheory ProbabilityTheory



variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]



variable [StandardBorelSpace alpha] [Nonempty alpha]

open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in
omit [StandardBorelSpace alpha] [Nonempty alpha] in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedNextObservationJoint_fst
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (iota : D ↪ NNReal) (n : ℕ) :
    (P.parameterizedNextObservationJoint e iota n).fst =
      P.parameterizedDenseTimePrefixKernel e iota n := by sorry
