-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsConservative_augmentedPrefixKernel_step
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsConservative.augmentedPrefixKernel_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:20:32.952333+00:00
-- url     : https://prove2.me/theorems/844e6e69-57b9-4479-bcd9-af6025805b6c
-- title:
--   Sampling the next observation conditionally and adjoining it gives the next prefix law
-- statement:
--   Sampling the next observation conditionally and adjoining it gives the next prefix law.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/DenseTime/PrefixRecursion.lean#L128-L181

import Definitions.Def_MarkovProcess_DenseTime_ConditionalKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixKernel
import Definitions.Def_MarkovProcess_DenseTime_PrefixRecursion
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Definitions.Def_MarkovProcess_Time_DenseTimeHistory
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
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
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup MarkovProcess.SubMarkovKernelSemigroup.IsConservative
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# One-step recursion for finite dense-time histories

This file identifies the result of adjoining one conditionally sampled observation to an
augmented finite history. It makes no infinite-process or path-regularity claim.
-/

open MeasureTheory ProbabilityTheory








variable {α : Type*} [MeasurableSpace α]













noncomputable section

variable {D α : Type*} [MeasurableSpace α]


variable [StandardBorelSpace α] [Nonempty α]

theorem MarkovProcess.SubMarkovKernelSemigroup.IsConservative.augmentedPrefixKernel_step (P : SubMarkovKernelSemigroup α)
    (hP : P.IsConservative) (e : ℕ ≃ D) (ι : D ↪ NNReal) (n : ℕ) :
    (((Kernel.id ×ₖ denseStep P hP e ι n) ∘ₖ augmentedPrefixKernel P e ι n).map
        (DenseTimeHistory.append n)) =
      augmentedPrefixKernel P e ι (n + 1) := by sorry
