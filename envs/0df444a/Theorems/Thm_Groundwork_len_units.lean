-- Prove2me | Theorems.Thm_Groundwork_len_units
-- name    : Groundwork.len_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:27:30.868784+00:00
-- url     : https://prove2.me/theorems/a23e81ff-0786-4a22-b894-7366287024f4
-- title:
--   Groundwork: len units
-- statement:
--   A list over `Unit` takes four symbols for each entry and two more at the end.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L92-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L92-L95

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

theorem Groundwork.len_units (w : List Unit) : len w = 4 * w.length + 2 := by sorry
