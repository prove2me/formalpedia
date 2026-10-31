-- Prove2me | Theorems.Thm_MarkovProcess_PositiveC0ContractiveResolvent_generatedSemigroup_apply_le_exp_mul
-- name    : MarkovProcess.PositiveC0ContractiveResolvent.generatedSemigroup_apply_le_exp_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:09.6557+00:00
-- url     : https://prove2.me/theorems/6b08f6e2-a9a6-4aab-ae15-adcd70a39f56
-- title:
--   MarkovProcess: generatedSemigroup_apply_le_exp_mul
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_PositiveC0Resolvent_c009f25c
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Metrizable.Urysohn

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exponential comparison under resolvent generation

A pointwise exponential supersolution estimate for every sufficiently large normalized positive
resolvent passes through the Poisson representation of the Yosida approximants and then through
their strong limit to the generated semigroup.  The represented kernel semigroup inherits the
same comparison for `C₀` observables.

Public declarations:

* `PositiveC0ContractiveResolvent.generatedSemigroup_apply_le_exp_mul`;
* `PositiveC0ContractiveResolvent.integral_kernelSemigroup_le_exp_mul`.

No comparison for indicators of arbitrary measurable sets is asserted.
-/

open Filter Set Topology
open scoped NNReal ZeroAtInfty
open NormedSpace

noncomputable section

namespace MarkovProcess

open _root_.MarkovProcess.Semigroup

namespace PositiveC0ContractiveResolvent

variable {X : Type*} [TopologicalSpace X]











section Kernel

variable [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]



end Kernel

end PositiveC0ContractiveResolvent

end MarkovProcess


open MarkovProcess
open MarkovProcess.PositiveC0ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Exponential comparison under resolvent generation

A pointwise exponential supersolution estimate for every sufficiently large normalized positive
resolvent passes through the Poisson representation of the Yosida approximants and then through
their strong limit to the generated semigroup.  The represented kernel semigroup inherits the
same comparison for `C₀` observables.

Public declarations:

* `PositiveC0ContractiveResolvent.generatedSemigroup_apply_le_exp_mul`;
* `PositiveC0ContractiveResolvent.integral_kernelSemigroup_le_exp_mul`.

No comparison for indicators of arbitrary measurable sets is asserted.
-/

open Filter Set Topology
open scoped NNReal ZeroAtInfty
open NormedSpace



open _root_.MarkovProcess.Semigroup


variable {X : Type*} [TopologicalSpace X]









open MarkovProcess.PositiveC0ContractiveResolvent in

theorem MarkovProcess.PositiveC0ContractiveResolvent.generatedSemigroup_apply_le_exp_mul
    (R : PositiveC0ContractiveResolvent X) (theta : ℝ) (v : C₀(X, ℝ))
    (hR : ∀ mu : PositiveShift, theta < (mu : ℝ) → ∀ x,
      (mu : ℝ) * R.toContractiveResolvent.operator mu v x ≤
        (mu : ℝ) / ((mu : ℝ) - theta) * v x)
    (t : NNReal) (x : X) :
    R.toContractiveResolvent.generatedSemigroup t v x ≤
      Real.exp (theta * (t : ℝ)) * v x := by sorry
