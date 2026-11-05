-- Prove2me | Theorems.Thm_Groundwork_len_nat_mono
-- name    : Groundwork.len_nat_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:38.191934+00:00
-- url     : https://prove2.me/theorems/fe5352cd-929f-48db-bfe6-c5a14cc681fe
-- title:
--   Groundwork: len nat mono
-- statement:
--   A larger natural number has a word at least as long.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L104-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L104-L105

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

theorem Groundwork.len_nat_mono {m n : ℕ} (h : m ≤ n) : len m ≤ len n := by sorry
