-- Prove2me | Theorems.Thm_Groundwork_Code_bijOn_enc
-- name    : Groundwork.Code.bijOn_enc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:41.392195+00:00
-- url     : https://prove2.me/theorems/ac4474b1-649f-407a-979b-81828b531e34
-- title:
--   Code: bij On enc
-- statement:
--   The Code construction uses the bij On enc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L41-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L41-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Definitions.Def_StepMachines_Math_CodeMore
set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}

theorem Groundwork.Code.bijOn_enc (c : Code S n) : Set.BijOn c.enc S c.D := by sorry
