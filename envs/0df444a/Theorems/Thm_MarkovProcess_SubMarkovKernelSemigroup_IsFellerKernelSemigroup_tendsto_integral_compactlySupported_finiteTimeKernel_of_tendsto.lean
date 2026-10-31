-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_tendsto_integral_compactlySupported_finiteTimeKernel_of_tendsto
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_integral_compactlySupported_finiteTimeKernel_of_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:52.395686+00:00
-- url     : https://prove2.me/theorems/7dab36a1-6fd8-4157-a7e5-365ddc2d8216
-- title:
--   MarkovProcess: tendsto_integral_compactlySupported_finiteTimeKernel_of_tendsto
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeJointCompactTestContinuity_c5428240
import Definitions.Def_MarkovProcess_V3H_FiniteTime_CoordinateProductActiveReduction_0fcd6a29
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.CompactlySupported
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Joint continuity of finite-time compact-test integrals

Finite-time integrals of compactly supported continuous tests vary continuously when both the
ordered observation times and the starting point vary. The empty coordinate family is included;
in that case the integral is constant, and no constant-one `C₀` function is introduced.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]



















end MarkovProcess.SubMarkovKernelSemigroup


open MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Joint continuity of finite-time compact-test integrals

Finite-time integrals of compactly supported continuous tests vary continuously when both the
ordered observation times and the starting point vary. The empty coordinate family is included;
in that case the integral is constant, and no constant-one `C₀` function is introduced.

This is finite-dimensional analytic infrastructure; no statement about path space is proved
here.  The continuous-path process is built in `Trajectory/`.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported


variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]















open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_integral_compactlySupported_finiteTimeKernel_of_tendsto
    {P : SubMarkovKernelSemigroup alpha} (hFeller : P.IsFellerKernelSemigroup)
    (hP : P.IsConservative) {X : Type*} {l : Filter X} {n : ℕ}
    {times : X → FiniteOrderedTimes n} {times₀ : FiniteOrderedTimes n}
    {x : X → alpha} {x₀ : alpha}
    (ht : ∀ i, Tendsto (fun a ↦ times a i) l (nhds (times₀ i)))
    (hx : Tendsto x l (nhds x₀)) (f : C_c(Fin n → alpha, ℝ)) :
    Tendsto (fun a ↦ ∫ path, f path ∂finiteTimeKernel P (times a) (x a)) l
      (nhds (∫ path, f path ∂finiteTimeKernel P times₀ x₀)) := by sorry
