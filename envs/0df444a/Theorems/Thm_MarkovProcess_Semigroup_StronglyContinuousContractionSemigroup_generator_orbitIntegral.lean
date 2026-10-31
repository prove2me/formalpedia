-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_generator_orbitIntegral
-- name    : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.generator_orbitIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:14.649932+00:00
-- url     : https://prove2.me/theorems/8305c406-439b-4956-b84d-a91a7a98002f
-- title:
--   MarkovProcess: generator_orbitIntegral
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_StrongOperatorLimit_428329b4
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The generator of a strongly continuous contraction semigroup

For `S : StronglyContinuousContractionSemigroup E` this file defines the generator domain
`S.generatorDomain`, the submodule of vectors `f` whose difference quotients
`t⁻¹ • (S t f - f)` converge as `t → 0⁺`, and the generator
`S.generator : S.generatorDomain →ₗ[ℝ] E` as that limit.  The main results are:

* `tendsto_generator`: the defining limit, and `generator_eq_of_tendsto`, its uniqueness;
* `operator_mem_generatorDomain` and `generator_operator`: the domain is invariant under every
  `S t`, and `S t` commutes with the generator;
* `tendsto_differenceQuotient_add`: every orbit `t ↦ S t f` of a vector in the domain is right
  differentiable at every time, with derivative `S t (S.generator f)`; its real-variable forms are
  `hasDerivWithinAt_Ioi` and `hasDerivWithinAt_Ici`, and at positive times the derivative is
  two-sided, `hasDerivAt_operator_toNNReal`;
* `operator_sub_eq_integral` and `exp_smul_operator_sub_eq_integral`: the fundamental identity
  and its exponentially weighted form;
* `orbitIntegral_mem_generatorDomain` and `generator_orbitIntegral`: for every vector `f`, the
  orbit integral `∫₀ᵗ S s f ds` lies in the domain with generator `S t f - f`; hence
  `dense_generatorDomain`, the domain is dense.

Times are `NNReal` throughout the library; the real-variable statements read the semigroup at
`Real.toNNReal s`.  The fundamental identity is what Dynkin's formula consumes.
-/

open Filter Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

section DifferenceQuotient













end DifferenceQuotient

section Domain







end Domain

section Generator

















end Generator

section Invariance







end Invariance

section RealVariable















variable [CompleteSpace E]





end RealVariable

section OrbitIntegral









variable [CompleteSpace E]















end OrbitIntegral

end

end MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# The generator of a strongly continuous contraction semigroup

For `S : StronglyContinuousContractionSemigroup E` this file defines the generator domain
`S.generatorDomain`, the submodule of vectors `f` whose difference quotients
`t⁻¹ • (S t f - f)` converge as `t → 0⁺`, and the generator
`S.generator : S.generatorDomain →ₗ[ℝ] E` as that limit.  The main results are:

* `tendsto_generator`: the defining limit, and `generator_eq_of_tendsto`, its uniqueness;
* `operator_mem_generatorDomain` and `generator_operator`: the domain is invariant under every
  `S t`, and `S t` commutes with the generator;
* `tendsto_differenceQuotient_add`: every orbit `t ↦ S t f` of a vector in the domain is right
  differentiable at every time, with derivative `S t (S.generator f)`; its real-variable forms are
  `hasDerivWithinAt_Ioi` and `hasDerivWithinAt_Ici`, and at positive times the derivative is
  two-sided, `hasDerivAt_operator_toNNReal`;
* `operator_sub_eq_integral` and `exp_smul_operator_sub_eq_integral`: the fundamental identity
  and its exponentially weighted form;
* `orbitIntegral_mem_generatorDomain` and `generator_orbitIntegral`: for every vector `f`, the
  orbit integral `∫₀ᵗ S s f ds` lies in the domain with generator `S t f - f`; hence
  `dense_generatorDomain`, the domain is dense.

Times are `NNReal` throughout the library; the real-variable statements read the semigroup at
`Real.toNNReal s`.  The fundamental identity is what Dynkin's formula consumes.
-/

open Filter Topology
open scoped NNReal



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)















variable [CompleteSpace E]









open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup in

theorem MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.generator_orbitIntegral (f : E) (t : NNReal) :
    S.generator ⟨S.orbitIntegral f t, S.orbitIntegral_mem_generatorDomain f t⟩ = S t f - f := by sorry
