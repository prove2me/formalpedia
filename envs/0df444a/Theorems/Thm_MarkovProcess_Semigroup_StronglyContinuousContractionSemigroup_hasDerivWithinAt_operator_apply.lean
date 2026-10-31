-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_hasDerivWithinAt_operator_apply
-- name    : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.hasDerivWithinAt_operator_apply
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:14.2679+00:00
-- url     : https://prove2.me/theorems/764cf1a7-6a86-49e3-b19d-9d6dae08012f
-- title:
--   MarkovProcess: hasDerivWithinAt_operator_apply
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
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
# The product rule for a semigroup acting along a curve

Let `S` be a strongly continuous contraction semigroup with generator `L` and let `v` be a curve
in the Banach space which is right differentiable at a time `s ≥ 0` and whose value `v s` lies in
the generator domain.  Then the evolved curve `y ↦ S y (v y)` is right differentiable at `s` with

  `d⁺/dy [ S y (v y) ] = S s (L (v s) + v' s)`.

The proof splits the increment as `S y (v y − v s) + S s (S (y − s) (v s) − v s)`.  The first
summand is handled by contractivity and strong continuity, the second is the difference quotient
that defines the generator; no differentiability of `y ↦ S y` in the operator norm is used, and
only the value of `v` at the single time `s` is required to lie in the domain.

Main results: `hasDerivWithinAt_operator_apply`.

Times are read from the real line at `Real.toNNReal`, as elsewhere in the library.  Nothing is
asserted about the two-sided derivative, which for a general curve fails at `s = 0`.
-/

open Filter Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)



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
# The product rule for a semigroup acting along a curve

Let `S` be a strongly continuous contraction semigroup with generator `L` and let `v` be a curve
in the Banach space which is right differentiable at a time `s ≥ 0` and whose value `v s` lies in
the generator domain.  Then the evolved curve `y ↦ S y (v y)` is right differentiable at `s` with

  `d⁺/dy [ S y (v y) ] = S s (L (v s) + v' s)`.

The proof splits the increment as `S y (v y − v s) + S s (S (y − s) (v s) − v s)`.  The first
summand is handled by contractivity and strong continuity, the second is the difference quotient
that defines the generator; no differentiability of `y ↦ S y` in the operator norm is used, and
only the value of `v` at the single time `s` is required to lie in the domain.

Main results: `hasDerivWithinAt_operator_apply`.

Times are read from the real line at `Real.toNNReal`, as elsewhere in the library.  Nothing is
asserted about the two-sided derivative, which for a general curve fails at `s = 0`.
-/

open Filter Topology
open scoped NNReal


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S : StronglyContinuousContractionSemigroup E)

open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup in

theorem MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.hasDerivWithinAt_operator_apply {v : ℝ → E} {v' : E} {s : ℝ} (hs : 0 ≤ s)
    (hmem : v s ∈ S.generatorDomain) (hv : HasDerivWithinAt v v' (Set.Ioi s) s) :
    HasDerivWithinAt (fun y : ℝ ↦ S (Real.toNNReal y) (v y))
      (S (Real.toNNReal s) (S.generator ⟨v s, hmem⟩ + v')) (Set.Ioi s) s := by sorry
