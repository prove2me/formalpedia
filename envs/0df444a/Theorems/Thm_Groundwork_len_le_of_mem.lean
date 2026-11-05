-- Prove2me | Theorems.Thm_Groundwork_len_le_of_mem
-- name    : Groundwork.len_le_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:27:29.926207+00:00
-- url     : https://prove2.me/theorems/9f4a631e-f853-4342-ac7b-656f84991d32
-- title:
--   Groundwork: len le of mem
-- statement:
--   The word of an entry is no longer than the word of the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L66-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L66-L73

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

theorem Groundwork.len_le_of_mem {a : α} {l : List α} (h : a ∈ l) : len a ≤ len l := by sorry
