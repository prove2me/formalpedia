-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_IsFellerKernelSemigroup_tendsto_kernelIntegral_finiteTimeKernel_one_map_eval
-- name    : MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_kernelIntegral_finiteTimeKernel_one_map_eval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:46.625682+00:00
-- url     : https://prove2.me/theorems/e46a9642-f787-4b9e-864f-23d706626205
-- title:
--   MarkovProcess: tendsto_kernelIntegral_finiteTimeKernel_one_map_eval
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeKernelContinuity_b2a7d2a7
import Definitions.Def_MarkovProcess_V3H_FiniteTime_Kernel_7ce8d73d
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

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Singleton finite-time Feller continuity

For a one-coordinate finite-time kernel, evaluation at the unique coordinate recovers the
transition kernel at that time.  Feller continuity therefore gives convergence of its `C₀` test
integrals as the observation time varies.  This is the base case for a recursive finite-time
continuity argument; no higher-dimensional continuity is asserted here.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty

namespace MarkovProcess
namespace SubMarkovKernelSemigroup

variable {alpha X : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]



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
# Singleton finite-time Feller continuity

For a one-coordinate finite-time kernel, evaluation at the unique coordinate recovers the
transition kernel at that time.  Feller continuity therefore gives convergence of its `C₀` test
integrals as the observation time varies.  This is the base case for a recursive finite-time
continuity argument; no higher-dimensional continuity is asserted here.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty


variable {alpha X : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]

open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.IsFellerKernelSemigroup.tendsto_kernelIntegral_finiteTimeKernel_one_map_eval
    {P : SubMarkovKernelSemigroup alpha} (hP : P.IsFellerKernelSemigroup)
    {l : Filter X} {times : X → FiniteOrderedTimes 1}
    {times0 : FiniteOrderedTimes 1}
    (ht : Tendsto (fun a ↦ times a 0) l (nhds (times0 0)))
    (f : C₀(alpha, ℝ)) (x : alpha) :
    Tendsto (fun a ↦ kernelIntegral
        ((finiteTimeKernel P (times a)).map (fun path ↦ path 0)) f x)
      l (nhds (kernelIntegral
        ((finiteTimeKernel P times0).map (fun path ↦ path 0)) f x)) := by sorry
