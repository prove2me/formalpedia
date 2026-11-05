-- Prove2me | Theorems.Thm_Groundwork_len_append
-- name    : Groundwork.len_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:32:51.811694+00:00
-- url     : https://prove2.me/theorems/4e60be34-2262-4b03-b19c-f4edf7ef97dd
-- title:
--   Groundwork: len append
-- statement:
--   The words of `l` and `l'` together have two symbols more than the word of `l ++ l'`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L56-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L56-L59

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

theorem Groundwork.len_append (l l' : List α) : len (l ++ l') + 2 = len l + len l' := by sorry
