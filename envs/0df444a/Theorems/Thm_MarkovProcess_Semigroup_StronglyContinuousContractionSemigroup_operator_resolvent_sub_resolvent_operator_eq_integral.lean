-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_operator_resolvent_sub_resolvent_operator_eq_integral
-- name    : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.operator_resolvent_sub_resolvent_operator_eq_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:35.685908+00:00
-- url     : https://prove2.me/theorems/32805458-4abe-4b01-a9f3-0e6c3ac80b0c
-- title:
--   MarkovProcess: operator_resolvent_sub_resolvent_operator_eq_integral
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_OrbitContinuity_8cf8e1f5
import Definitions.Def_MarkovProcess_V3H_Semigroup_Resolvent_323559dd
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Comparing two semigroups through their resolvents

Two strongly continuous contraction semigroups `S` and `S'` on the same Banach space have, in
general, unrelated generator domains, so the naive Duhamel comparison of their orbits is not
available.  Inserting one resolvent of each semigroup repairs this: the curve

  `y ↦ S y (R_μ (S' (t − y) (R'_μ z)))`,

where `R_μ` and `R'_μ` are the resolvents of `S` and of `S'` at a positive shift `μ`, takes values
in the generator domain of `S` at every time, is differentiable because `R'_μ z` lies in the
generator domain of `S'`, and its derivative telescopes to the difference of the two resolvents:

  `S t (R_μ (R'_μ z)) − R_μ (S' t (R'_μ z)) = ∫₀ᵗ S y ((R_μ − R'_μ) (S' (t − y) z)) dy.`

Consequently the left-hand side is bounded by `t` times the largest value of `‖(R_μ − R'_μ) v‖`
over the orbit `{S' u z : 0 ≤ u ≤ t}`, which is a compact set.  This is the mechanism behind the
Trotter--Kato theorem in `Semigroup/TrotterKato.lean`.

Main results: `operator_resolvent_sub_resolvent_operator_eq_integral`,
`norm_operator_resolvent_sub_resolvent_operator_le`.

Both semigroups are read at the same shift `μ`; nothing is asserted when the two resolvents are
taken at different shifts, and no relation between the two generators is assumed.
-/

open Filter MeasureTheory Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]







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
# Comparing two semigroups through their resolvents

Two strongly continuous contraction semigroups `S` and `S'` on the same Banach space have, in
general, unrelated generator domains, so the naive Duhamel comparison of their orbits is not
available.  Inserting one resolvent of each semigroup repairs this: the curve

  `y ↦ S y (R_μ (S' (t − y) (R'_μ z)))`,

where `R_μ` and `R'_μ` are the resolvents of `S` and of `S'` at a positive shift `μ`, takes values
in the generator domain of `S` at every time, is differentiable because `R'_μ z` lies in the
generator domain of `S'`, and its derivative telescopes to the difference of the two resolvents:

  `S t (R_μ (R'_μ z)) − R_μ (S' t (R'_μ z)) = ∫₀ᵗ S y ((R_μ − R'_μ) (S' (t − y) z)) dy.`

Consequently the left-hand side is bounded by `t` times the largest value of `‖(R_μ − R'_μ) v‖`
over the orbit `{S' u z : 0 ≤ u ≤ t}`, which is a compact set.  This is the mechanism behind the
Trotter--Kato theorem in `Semigroup/TrotterKato.lean`.

Main results: `operator_resolvent_sub_resolvent_operator_eq_integral`,
`norm_operator_resolvent_sub_resolvent_operator_le`.

Both semigroups are read at the same shift `μ`; nothing is asserted when the two resolvents are
taken at different shifts, and no relation between the two generators is assumed.
-/

open Filter MeasureTheory Topology
open scoped NNReal



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]



open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup in

theorem MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.operator_resolvent_sub_resolvent_operator_eq_integral
    (S S' : StronglyContinuousContractionSemigroup E) (μ : PositiveShift) (t : NNReal) (z : E) :
    S t (S.resolvent μ (S'.resolvent μ z)) - S.resolvent μ (S' t (S'.resolvent μ z)) =
      ∫ y in (0 : ℝ)..(t : ℝ), S (Real.toNNReal y)
        (S.resolvent μ (S' (Real.toNNReal ((t : ℝ) - y)) z) -
          S'.resolvent μ (S' (Real.toNNReal ((t : ℝ) - y)) z)) := by sorry
