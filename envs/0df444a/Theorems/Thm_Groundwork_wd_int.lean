-- Prove2me | Theorems.Thm_Groundwork_wd_int
-- name    : Groundwork.wd_int
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:13.953179+00:00
-- url     : https://prove2.me/theorems/cb13b5c7-64a6-44fd-9e4c-d39504481069
-- title:
--   Groundwork: wd int
-- statement:
--   An integer is written as the pair of its sign (`true` if negative) and its absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L31-L31

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

theorem Groundwork.wd_int (z : ℤ) : wd z = wd (decide (z < 0), z.natAbs) := by sorry
