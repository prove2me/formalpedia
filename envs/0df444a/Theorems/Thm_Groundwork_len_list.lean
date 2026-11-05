-- Prove2me | Theorems.Thm_Groundwork_len_list
-- name    : Groundwork.len_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:00.80056+00:00
-- url     : https://prove2.me/theorems/d715f00d-bb30-46c2-ab42-09872c2bd72a
-- title:
--   Groundwork: len list
-- statement:
--   The word of a list has the words of its entries, two brackets for each entry and two more at the
--   end.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L51-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L51-L54

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

theorem Groundwork.len_list (l : List α) : len l = (l.map fun a => len a + 2).sum + 2 := by sorry
