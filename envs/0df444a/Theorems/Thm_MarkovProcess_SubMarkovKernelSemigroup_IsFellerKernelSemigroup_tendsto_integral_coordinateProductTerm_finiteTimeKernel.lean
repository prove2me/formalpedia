-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_tendsto_integral_coordinateProductTerm_finiteTimeKernel
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_integral_coordinateProductTerm_finiteTimeKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T14:20:28.996497+00:00
-- url     : https://prove2.me/theorems/5c18a2ac-f39a-4bf7-9b5e-a9d1883d5b9e
-- title:
--   Continuity of finite-time coordinate-product integrals
-- statement:
--   The finite-time integral of a coordinate-product term varies continuously when every
--   ordered time coordinate varies continuously.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Feller/CoordinateProductContinuity.lean#L31-L116

import Definitions.Def_MarkovProcess_Feller_BackwardC0Recursion
import Definitions.Def_MarkovProcess_Feller_Semigroup
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductActiveReduction
import Definitions.Def_MarkovProcess_FiniteTime_CoordinateProductNormalization
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
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
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma
open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Continuity of finite-time integrals of coordinate-product terms

This file proves continuity, under coordinatewise convergence of ordered times, of the
finite-time-kernel integral of one `PiContinuousMap.CoordinateProductTerm`.  The proof reduces
to the coordinates on which the term has factors and applies the backward `C₀` recursion.

When there are no active coordinates, the integrand is its scalar coefficient.  That branch
uses conservativity to identify the finite-time law as a probability measure; in particular,
it never attempts to construct a constant-one element of `C₀`.  This is finite-dimensional
analytic infrastructure; no statement about path space is proved here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators


variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_integral_coordinateProductTerm_finiteTimeKernel
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes n} {times0 : FiniteOrderedTimes n}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times0 i)))
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha) (x : alpha) :
    Tendsto (fun a ↦ ∫ path, term.toContinuousMap path ∂finiteTimeKernel P (times a) x) l
      (nhds (∫ path, term.toContinuousMap path ∂finiteTimeKernel P times0 x)) := by sorry
