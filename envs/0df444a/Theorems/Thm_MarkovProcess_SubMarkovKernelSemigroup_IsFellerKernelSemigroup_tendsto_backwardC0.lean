-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_tendsto_backwardC0
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_backwardC0
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:16:28.370712+00:00
-- url     : https://prove2.me/theorems/f5448b4f-755c-48fc-a28f-5336bc92e40f
-- title:
--   Continuity of backward C₀ recursion
-- statement:
--   The backward recursion is continuous in the `C₀` norm under coordinatewise convergence of a
--   nonempty ordered time family.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/BackwardC0Recursion.lean#L60-L84

import Definitions.Def_MarkovProcess_Feller_BackwardC0Recursion
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_C0_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_Integral_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Semigroup_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Backward `C₀` recursion for finite Feller transitions

An ordered nonempty family of one-coordinate `C₀` factors determines a backward semigroup
recursion: evolve the last factors relative to the first time, multiply by the first factor, and
then evolve from the starting state to the first time.  The recursion varies continuously in the
`C₀` norm when every ordered observation time converges.

This file contains only the analytic recursion and its continuity.  Its identification with an
integral against a finite-time kernel is in `Feller/BackwardC0Integral.lean`; no statement about
path space is proved here.
-/

open Filter Topology
open scoped NNReal ZeroAtInfty


variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_backwardC0
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes (n + 1)}
    {times0 : FiniteOrderedTimes (n + 1)}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    Tendsto (fun a ↦ hP.backwardC0 (times a) factors) l
      (nhds (hP.backwardC0 times0 factors)) := by sorry
