-- Prove2me | Theorems.Thm_Groundwork_len_drop_le
-- name    : Groundwork.len_drop_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:33.04956+00:00
-- url     : https://prove2.me/theorems/677ddc2b-f34c-41f9-aadd-7213cf8bc5b4
-- title:
--   Groundwork: len drop le
-- statement:
--   The Groundwork construction uses the len drop le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L77-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/EncLemmas.lean#L77-L81

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

theorem Groundwork.len_drop_le (l : List α) (k : ℕ) : len (l.drop k) ≤ len l := by sorry
