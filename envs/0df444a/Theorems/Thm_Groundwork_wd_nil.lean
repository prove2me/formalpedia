-- Prove2me | Theorems.Thm_Groundwork_wd_nil
-- name    : Groundwork.wd_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:27.415959+00:00
-- url     : https://prove2.me/theorems/184c8459-b5d6-4f0d-bf8f-020faa35d128
-- title:
--   Groundwork: wd nil
-- statement:
--   The Groundwork construction uses the wd nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L23-L23
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L23-L23

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

theorem Groundwork.wd_nil : wd ([] : List α) = [.L, .R] := by sorry
