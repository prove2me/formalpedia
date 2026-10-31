-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_tendstoUniformly_integral_coordinateProduct_finiteTimeKernel
-- name    : MarkovProcess.SubMarkovKernelSemigroup.tendstoUniformly_integral_coordinateProduct_finiteTimeKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:54.077791+00:00
-- url     : https://prove2.me/theorems/4a32a4d4-91ab-4cc6-a567-8a9931ace102
-- title:
--   MarkovProcess: tendstoUniformly_integral_coordinateProduct_finiteTimeKernel
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
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
# Convergence of the backward `C₀` recursion along a family of semigroups

The backward recursion of `Feller/BackwardC0Recursion.lean` evolves a nonempty ordered family of
one-coordinate `C₀` factors through the transitions of one Feller kernel semigroup.  Here the
family of times and the factors are held fixed and the *semigroup* varies along a filter: if the
`C₀` semigroups converge strongly, so does the backward recursion, in the `C₀` norm.  The
induction is one line per step: contractivity makes the outer transition insensitive to the
error accumulated by the inner one.

Since the `C₀` norm is the supremum norm, this is exactly convergence of the coordinate-product
integrals against the finite-time kernels, uniformly in the starting point.

Main results: `tendsto_backwardC0_of_tendsto_c0Semigroup`,
`tendstoUniformly_integral_coordinateProduct_finiteTimeKernel`.

The factors and the observation times are fixed; nothing is asserted when they vary along the
filter as well, and no rate of convergence is claimed.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty BigOperators

namespace MarkovProcess

section Uniform

variable {alpha : Type*} [TopologicalSpace alpha] {iota : Type*} {l : Filter iota}



end Uniform

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}





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
# Convergence of the backward `C₀` recursion along a family of semigroups

The backward recursion of `Feller/BackwardC0Recursion.lean` evolves a nonempty ordered family of
one-coordinate `C₀` factors through the transitions of one Feller kernel semigroup.  Here the
family of times and the factors are held fixed and the *semigroup* varies along a filter: if the
`C₀` semigroups converge strongly, so does the backward recursion, in the `C₀` norm.  The
induction is one line per step: contractivity makes the outer transition insensitive to the
error accumulated by the inner one.

Since the `C₀` norm is the supremum norm, this is exactly convergence of the coordinate-product
integrals against the finite-time kernels, uniformly in the starting point.

Main results: `tendsto_backwardC0_of_tendsto_c0Semigroup`,
`tendstoUniformly_integral_coordinateProduct_finiteTimeKernel`.

The factors and the observation times are fixed; nothing is asserted when they vary along the
filter as well, and no rate of convergence is claimed.
-/

open Filter MeasureTheory Topology
open scoped NNReal ZeroAtInfty BigOperators




variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}



open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.tendstoUniformly_integral_coordinateProduct_finiteTimeKernel
    {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hQ : Q.IsFellerKernelSemigroup)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes (n + 1)) (factors : Fin (n + 1) → C₀(alpha, ℝ)) :
    TendstoUniformly
      (fun i x ↦ ∫ path, ∏ j, factors j (path j) ∂finiteTimeKernel (P i) times x)
      (fun x ↦ ∫ path, ∏ j, factors j (path j) ∂finiteTimeKernel Q times x) l := by sorry
