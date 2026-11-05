-- Prove2me | Theorems.Thm_Groundwork_wd_none
-- name    : Groundwork.wd_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:30.727249+00:00
-- url     : https://prove2.me/theorems/32ec1d5f-aa61-44cf-8307-e559efd0ecc3
-- title:
--   Groundwork: wd none
-- statement:
--   The Groundwork construction uses the wd none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L25-L25
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L25-L25

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

theorem Groundwork.wd_none : wd (none : Option α) = [.L, .R] := by sorry
