-- Prove2me | Theorems.Thm_Groundwork_PolyT_lookup_polyT
-- name    : Groundwork.PolyT.lookup_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:27:12.613287+00:00
-- url     : https://prove2.me/theorems/a8364f94-987a-41df-8ffc-482a593f24e9
-- title:
--   Poly T: lookup poly T
-- statement:
--   Reading a table is polynomial-time: the list is fixed, so this is a fixed chain of tests.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L41-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L41-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Definitions.Def_ToTuring_Lib_Table
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε ζ : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε] [Enc ζ]

theorem Groundwork.PolyT.lookup_polyT [DecidableEq β] [EqT β] (F : β → γ) (d : γ) (l : List β) : PolyT (lookup F d l) := by sorry
