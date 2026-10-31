-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_eq_zero_of_generator_eq_smul
-- name    : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.eq_zero_of_generator_eq_smul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:36.266725+00:00
-- url     : https://prove2.me/theorems/db83d4fc-d0c9-4495-9a33-7bf0a728df76
-- title:
--   MarkovProcess: eq_zero_of_generator_eq_smul
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_GeneratorInjectivity_5e725388
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Eigenvectors of a generator, and injectivity of `μ - L`

Let `S` be a strongly continuous contraction semigroup with generator `L`.  If `f` lies in the
generator domain with `L f = μ f`, then the orbit of `f` is the scalar exponential
`S t f = exp (μ t) f`: the defect `w t = S t f - exp (μ t) f` vanishes at `t = 0` and has right
derivative `μ w t`, so Grönwall's inequality forces it to vanish
(`operator_eq_exp_smul_of_generator_eq_smul`).

Since `S` is contractive, an eigenvalue `μ > 0` therefore forces `f = 0`
(`eq_zero_of_generator_eq_smul`); equivalently, `μ - L` is injective on the generator domain
(`eq_of_smul_sub_generator_eq`).  This is the uniqueness half of the assertion that the resolvent
`(μ - L)⁻¹` is a well-defined operator.
-/

open Filter Set Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)















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
# Eigenvectors of a generator, and injectivity of `μ - L`

Let `S` be a strongly continuous contraction semigroup with generator `L`.  If `f` lies in the
generator domain with `L f = μ f`, then the orbit of `f` is the scalar exponential
`S t f = exp (μ t) f`: the defect `w t = S t f - exp (μ t) f` vanishes at `t = 0` and has right
derivative `μ w t`, so Grönwall's inequality forces it to vanish
(`operator_eq_exp_smul_of_generator_eq_smul`).

Since `S` is contractive, an eigenvalue `μ > 0` therefore forces `f = 0`
(`eq_zero_of_generator_eq_smul`); equivalently, `μ - L` is injective on the generator domain
(`eq_of_smul_sub_generator_eq`).  This is the uniqueness half of the assertion that the resolvent
`(μ - L)⁻¹` is a well-defined operator.
-/

open Filter Set Topology
open scoped NNReal



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)











open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup in

theorem MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.eq_zero_of_generator_eq_smul {μ : ℝ} (hμ : 0 < μ) (f : S.generatorDomain)
    (hgen : S.generator f = μ • (f : E)) : (f : E) = 0 := by sorry
