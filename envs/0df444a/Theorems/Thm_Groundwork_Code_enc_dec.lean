-- Prove2me | Theorems.Thm_Groundwork_Code_enc_dec
-- name    : Groundwork.Code.enc_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:33.922643+00:00
-- url     : https://prove2.me/theorems/35f10b93-e023-4168-959a-9c2335e8fa85
-- title:
--   Code: enc dec
-- statement:
--   The Code construction uses the enc dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L33-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L33-L34

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

theorem Groundwork.Code.enc_dec (c : Code S n) {w : List Bool} (hw : w ∈ c.D) : c.enc (c.dec w) = w := by sorry
