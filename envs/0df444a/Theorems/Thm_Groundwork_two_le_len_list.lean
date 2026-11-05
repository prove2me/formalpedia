-- Prove2me | Theorems.Thm_Groundwork_two_le_len_list
-- name    : Groundwork.two_le_len_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:40.668201+00:00
-- url     : https://prove2.me/theorems/62553bc4-7131-4e4a-8b71-1dbf5e4cc9e5
-- title:
--   Groundwork: two le len list
-- statement:
--   The word of a list has at least its two brackets.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L75-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L75-L76

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

theorem Groundwork.two_le_len_list (l : List α) : 2 ≤ len l := by sorry
