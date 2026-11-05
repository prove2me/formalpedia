-- Prove2me | Theorems.Thm_Groundwork_Code_dec_inj
-- name    : Groundwork.Code.dec_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:37.890922+00:00
-- url     : https://prove2.me/theorems/b9066752-7a12-4738-bfbd-1c3c15a96958
-- title:
--   Code: dec inj
-- statement:
--   The Code construction uses the dec inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L36-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L36-L37

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

theorem Groundwork.Code.dec_inj (c : Code S n) {w w' : List Bool} (hw : w ∈ c.D) (hw' : w' ∈ c.D) :
    c.dec w = c.dec w' ↔ w = w' := by sorry
