-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_ext_of_generator
-- name    : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.ext_of_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:23.745048+00:00
-- url     : https://prove2.me/theorems/38429250-f38a-45a7-870e-7e022eb1b177
-- title:
--   MarkovProcess: ext_of_generator
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_GeneratorUniqueness_43727223
import Definitions.Def_MarkovProcess_V3H_Semigroup_Generator_18e72ab8
import Definitions.Def_MarkovProcess_V3H_Semigroup_OrbitContinuity_8cf8e1f5
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
# The generator determines the semigroup

Two strongly continuous contraction semigroups with the same generator domain and the same
generator on it are equal (`ext_of_generator`).

The proof interpolates between the two evolutions: for a vector `f` of the common domain and a
fixed time `t`, the path `s ↦ S (t - s) (T s f)` on `[0, t]` is continuous and has right
derivative zero, because

`S (t - s - h) (T (s + h) f) - S (t - s) (T s f)
    = S (t - s - h) ((T h - 1) (T s f) - (S h - 1) (T s f))`,

and the two difference quotients on the right converge to the common value of the generators at
`T s f`.  Grönwall's inequality then makes the path constant, and its two endpoints are `S t f`
and `T t f`.  Density of the generator domain extends the identity to the whole space.
-/

open Filter Set Topology
open scoped NNReal

namespace MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S T : StronglyContinuousContractionSemigroup E)













variable [CompleteSpace E]



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
# The generator determines the semigroup

Two strongly continuous contraction semigroups with the same generator domain and the same
generator on it are equal (`ext_of_generator`).

The proof interpolates between the two evolutions: for a vector `f` of the common domain and a
fixed time `t`, the path `s ↦ S (t - s) (T s f)` on `[0, t]` is continuous and has right
derivative zero, because

`S (t - s - h) (T (s + h) f) - S (t - s) (T s f)
    = S (t - s - h) ((T h - 1) (T s f) - (S h - 1) (T s f))`,

and the two difference quotients on the right converge to the common value of the generators at
`T s f`.  Grönwall's inequality then makes the path constant, and its two endpoints are `S t f`
and `T t f`.  Density of the generator domain extends the identity to the whole space.
-/

open Filter Set Topology
open scoped NNReal



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (S T : StronglyContinuousContractionSemigroup E)













variable [CompleteSpace E]

open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup in

theorem MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.ext_of_generator (hdom : S.generatorDomain = T.generatorDomain)
    (hgen : ∀ (f : E) (hS : f ∈ S.generatorDomain) (hT : f ∈ T.generatorDomain),
      S.generator ⟨f, hS⟩ = T.generator ⟨f, hT⟩) :
    S = T := by sorry
