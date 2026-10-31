-- Prove2me | Theorems.Thm_MarkovProcess_ParameterizedSubMarkovKernelSemigroup_parameterizedDenseTimePrefixKernel_map_restrictPath
-- name    : MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedDenseTimePrefixKernel_map_restrictPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:34:20.487988+00:00
-- url     : https://prove2.me/theorems/c2353fc8-3860-44ef-9726-d4f6a30862c5
-- title:
--   MarkovProcess: parameterizedDenseTimePrefixKernel_map_restrictPath
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_PrefixKernel_a192bbea
import Definitions.Def_MarkovProcess_V3H_Parameterized_DenseTimePrefixKernel_12387c59
import Definitions.Def_MarkovProcess_V3H_Parameterized_FiniteTimeProjectiveFamily_8428346b
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
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Parameterized kernels on finite prefixes of a countable time enumeration

This file constructs jointly measurable kernels on the first `n` points of an arbitrary
enumeration. Coordinates remain in enumeration order; the enumeration need not be monotone in
physical time. Fiberwise conservativity is used only for Markovness and prefix consistency.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ParameterizedSubMarkovKernelSemigroup

noncomputable section

variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]











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
# Parameterized kernels on finite prefixes of a countable time enumeration

This file constructs jointly measurable kernels on the first `n` points of an arbitrary
enumeration. Coordinates remain in enumeration order; the enumeration need not be monotone in
physical time. Fiberwise conservativity is used only for Markovness and prefix consistency.
-/

open MeasureTheory ProbabilityTheory



variable {Theta D alpha : Type*} [MeasurableSpace Theta] [MeasurableSpace alpha]









open MarkovProcess.ParameterizedSubMarkovKernelSemigroup in

theorem MarkovProcess.ParameterizedSubMarkovKernelSemigroup.parameterizedDenseTimePrefixKernel_map_restrictPath
    (P : ParameterizedSubMarkovKernelSemigroup Theta alpha)
    (hP : ∀ theta, (P.toSubMarkovKernelSemigroup theta).IsConservative)
    (e : ℕ ≃ D) (ι : D ↪ NNReal) {m n : ℕ} (h : m ≤ n) :
    P.parameterizedDenseTimePrefixKernel e ι m =
      (P.parameterizedDenseTimePrefixKernel e ι n).map
        (FiniteOrderedTimes.restrictPath (Fin.castLEOrderEmb h)) := by sorry
