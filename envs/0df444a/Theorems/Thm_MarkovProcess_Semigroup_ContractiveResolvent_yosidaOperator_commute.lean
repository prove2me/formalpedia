-- Prove2me | Theorems.Thm_MarkovProcess_Semigroup_ContractiveResolvent_yosidaOperator_commute
-- name    : MarkovProcess.Semigroup.ContractiveResolvent.yosidaOperator_commute
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:24:17.902322+00:00
-- url     : https://prove2.me/theorems/02df924d-56bf-4fa5-99d6-7ac4add95319
-- title:
--   MarkovProcess: yosidaOperator_commute
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Semigroup_Basic_fec91841
import Definitions.Def_MarkovProcess_V3H_Semigroup_ContractiveResolvent_4e63c9ca
import Definitions.Def_MarkovProcess_V3H_Semigroup_ExponentialBounds_642305eb
import Definitions.Def_MarkovProcess_V3H_Semigroup_YosidaApproximation_2f7df37a
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Bounded Yosida approximations

For a contractive resolvent `R`, this file defines the bounded generator
`G_α = α (α R_α - I)` and its exponential contraction semigroup.  It also
records commutation and the exact formula on the range of a fixed resolvent.
-/

open Filter Topology
open NormedSpace

noncomputable section

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Head-class caches for the operator type.  Every repeated closed instance
search in this file is rooted at `E →L[ℝ] E`; resolving each head class once
here stops the normed-hierarchy walk on `E` from being replayed at every `•`,
`exp` and `comp`. -/









section CompleteSpace

variable [CompleteSpace E]















end CompleteSpace









end ContractiveResolvent

end MarkovProcess.Semigroup


open MarkovProcess
open MarkovProcess.Semigroup
open MarkovProcess.Semigroup.ContractiveResolvent
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Bounded Yosida approximations

For a contractive resolvent `R`, this file defines the bounded generator
`G_α = α (α R_α - I)` and its exponential contraction semigroup.  It also
records commutation and the exact formula on the range of a fixed resolvent.
-/

open Filter Topology
open NormedSpace




variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Head-class caches for the operator type.  Every repeated closed instance
search in this file is rooted at `E →L[ℝ] E`; resolving each head class once
here stops the normed-hierarchy walk on `E` from being replayed at every `•`,
`exp` and `comp`. -/












open MarkovProcess.Semigroup.ContractiveResolvent in

theorem MarkovProcess.Semigroup.ContractiveResolvent.yosidaOperator_commute (R : ContractiveResolvent E)
    (α β : PositiveShift) (s t : NNReal) :
    Commute (R.yosidaOperator α s) (R.yosidaOperator β t) := by sorry
