-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_StronglyContinuousContractionSemigroup_ext
-- name    : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.ext
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T13:13:34.296956+00:00
-- url     : https://prove2.me/theorems/4b8f2ee6-23bb-4a02-af71-5367c0511e0e
-- title:
--   Extensionality of strongly continuous contraction semigroups
-- statement:
--   Two strongly continuous contraction semigroups on the same real normed vector space are equal if their bounded linear evolution operators agree at every nonnegative time. This supplies the standard extensionality principle for the semigroup data type in Scott Armstrong's MarkovProcess formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Semigroup/Basic.lean#L37-L46

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_MarkovProcess_Semigroup_Basic

open Filter Topology
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

@[ext]
theorem MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.ext {S T : StronglyContinuousContractionSemigroup E}
    (h : ∀ t, S t = T t) : S = T := by sorry
