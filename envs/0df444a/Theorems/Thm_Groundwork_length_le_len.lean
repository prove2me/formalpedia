-- Prove2me | Theorems.Thm_Groundwork_length_le_len
-- name    : Groundwork.length_le_len
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:27:15.172729+00:00
-- url     : https://prove2.me/theorems/9a493047-377b-48f6-a419-3d116a0beaab
-- title:
--   Groundwork: length le len
-- statement:
--   A list has at most as many entries as its word has symbols.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L61-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L61-L64

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

theorem Groundwork.length_le_len (l : List α) : l.length ≤ len l := by sorry
