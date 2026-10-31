-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_tendsto
-- name    : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:12.235989+00:00
-- url     : https://prove2.me/theorems/7dcc6351-c60c-40fe-9f55-a232210b60a8
-- title:
--   MarkovProcess: tendsto
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Mathlib.Analysis.Normed.Operator.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strongly continuous contraction semigroups

This file provides a small reusable interface for strongly continuous contraction
semigroups on real normed spaces, parametrized by nonnegative real time.
-/

open Filter Topology

namespace MarkovProcess.Semigroup



namespace StronglyContinuousContractionSemigroup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





variable (S : StronglyContinuousContractionSemigroup E)

























end StronglyContinuousContractionSemigroup

end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Strongly continuous contraction semigroups

This file provides a small reusable interface for strongly continuous contraction
semigroups on real normed spaces, parametrized by nonnegative real time.
-/

open Filter Topology





variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





variable (S : StronglyContinuousContractionSemigroup E)



















open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup in

theorem MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.tendsto (t : NNReal) (x : E) :
    Tendsto (fun s ↦ S s x) (nhds t) (nhds (S t x)) := by sorry
