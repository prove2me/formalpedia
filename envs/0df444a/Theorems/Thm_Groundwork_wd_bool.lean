-- Prove2me | Theorems.Thm_Groundwork_wd_bool
-- name    : Groundwork.wd_bool
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:21.210181+00:00
-- url     : https://prove2.me/theorems/2fdd2f20-cdac-4729-be54-60c9e3eb332a
-- title:
--   Groundwork: wd bool
-- statement:
--   The Groundwork construction uses the wd bool property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L29-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L29-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Enc
import Definitions.Def_ToTuring_EncLemmas
set_option autoImplicit false
section
section
open Groundwork
open TM Enc
variable {α β : Type} [Enc α] [Enc β]

theorem Groundwork.wd_bool (b : Bool) : wd b = [.bit b] := by sorry
