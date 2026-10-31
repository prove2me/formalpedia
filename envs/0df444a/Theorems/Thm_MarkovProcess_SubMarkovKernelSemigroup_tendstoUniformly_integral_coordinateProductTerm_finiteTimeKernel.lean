-- Prove2me | Theorems.Thm_MarkovProcess_SubMarkovKernelSemigroup_tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel
-- name    : MarkovProcess.SubMarkovKernelSemigroup.tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:50.403022+00:00
-- url     : https://prove2.me/theorems/f913ba78-9dd3-461f-b17a-61e112b2afd5
-- title:
--   MarkovProcess: tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Feller_BackwardC0Integral_1512e54f
import Definitions.Def_MarkovProcess_V3H_Feller_FiniteTimeConvergence_4d25bc20
import Definitions.Def_MarkovProcess_V3H_FiniteTime_CoordinateProductActiveReduction_0fcd6a29
import Definitions.Def_MarkovProcess_V3H_FiniteTime_FiniteProductCoordinateNormalForm_522d03e6
import Definitions.Def_MarkovProcess_V3H_FiniteTime_KernelRestriction_041bf9e5
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
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
# Convergence of finite-time laws along a family of Feller semigroups

Let `P i` be conservative Feller kernel semigroups whose `C₀` semigroups converge strongly to
that of a conservative Feller kernel semigroup `Q`.  Then, at every fixed finite ordered family
of observation times, the finite-time laws converge, uniformly in the starting point:

* for a coordinate-product term, by reduction to the coordinates carrying a factor and the
  backward `C₀` recursion (`Feller/BackwardC0Convergence.lean`); a term with no active
  coordinate integrates to its coefficient because the finite-time law is a probability measure;
* for a finite coordinate polynomial, by linearity;
* for an arbitrary compactly supported continuous test, by uniform approximation with coordinate
  polynomials (`FiniteTime/FiniteProductCoordinateNormalForm.lean`), the approximation error
  being uniform because the laws are probability measures.

Main results: `tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel`,
`tendstoUniformly_integral_coordinatePolynomial_finiteTimeKernel`,
`tendstoUniformly_integral_compactlySupported_finiteTimeKernel`.

The observation times are fixed throughout; nothing is asserted for test functions that are only
bounded and continuous, which needs the tightness of the limiting law and is therefore not
uniform in the starting point.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported

namespace MarkovProcess

section UniformAlgebra

variable {beta : Type*} {iota : Type*} {l : Filter iota}







end UniformAlgebra

namespace SubMarkovKernelSemigroup

variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}

section Integrability





end Integrability

section ActiveReduction









end ActiveReduction

variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}





section CompactTest

variable [SecondCountableTopology alpha]



end CompactTest

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
# Convergence of finite-time laws along a family of Feller semigroups

Let `P i` be conservative Feller kernel semigroups whose `C₀` semigroups converge strongly to
that of a conservative Feller kernel semigroup `Q`.  Then, at every fixed finite ordered family
of observation times, the finite-time laws converge, uniformly in the starting point:

* for a coordinate-product term, by reduction to the coordinates carrying a factor and the
  backward `C₀` recursion (`Feller/BackwardC0Convergence.lean`); a term with no active
  coordinate integrates to its coefficient because the finite-time law is a probability measure;
* for a finite coordinate polynomial, by linearity;
* for an arbitrary compactly supported continuous test, by uniform approximation with coordinate
  polynomials (`FiniteTime/FiniteProductCoordinateNormalForm.lean`), the approximation error
  being uniform because the laws are probability measures.

Main results: `tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel`,
`tendstoUniformly_integral_coordinatePolynomial_finiteTimeKernel`,
`tendstoUniformly_integral_compactlySupported_finiteTimeKernel`.

The observation times are fixed throughout; nothing is asserted for test functions that are only
bounded and continuous, which needs the tightness of the limiting law and is therefore not
uniform in the starting point.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ZeroAtInfty BigOperators CompactlySupported




variable {alpha : Type*} [TopologicalSpace alpha] [MeasurableSpace alpha]
  [BorelSpace alpha] [LocallyCompactSpace alpha] [T2Space alpha]
variable {iota : Type*} {l : Filter iota}



variable {P : iota → SubMarkovKernelSemigroup alpha} {Q : SubMarkovKernelSemigroup alpha}

open MarkovProcess.SubMarkovKernelSemigroup in

theorem MarkovProcess.SubMarkovKernelSemigroup.tendstoUniformly_integral_coordinateProductTerm_finiteTimeKernel
    (hP : ∀ i, (P i).IsFellerKernelSemigroup) (hPc : ∀ i, (P i).IsConservative)
    (hQ : Q.IsFellerKernelSemigroup) (hQc : Q.IsConservative)
    (hconv : ∀ (t : NNReal) (f : C₀(alpha, ℝ)),
      Tendsto (fun i ↦ (hP i).c0Semigroup t f) l (nhds (hQ.c0Semigroup t f)))
    {n : ℕ} (times : FiniteOrderedTimes n)
    (term : PiContinuousMap.CoordinateProductTerm (Fin n) alpha) :
    TendstoUniformly
      (fun i x ↦ ∫ path, term.toContinuousMap path ∂finiteTimeKernel (P i) times x)
      (fun x ↦ ∫ path, term.toContinuousMap path ∂finiteTimeKernel Q times x) l := by sorry
