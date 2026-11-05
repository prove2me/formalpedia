-- Prove2me | Theorems.Thm_Groundwork_PolyT_table
-- name    : Groundwork.PolyT.table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:27:55.995322+00:00
-- url     : https://prove2.me/theorems/9bc87584-f5dc-4a7a-9942-24f96fd02af8
-- title:
--   Poly T: table
-- statement:
--   Every function on a finite type with a polynomial-time equality test is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L47-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L47-L52

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

theorem Groundwork.PolyT.table [Finite β] [DecidableEq β] [EqT β] (F : β → γ) : PolyT F := by sorry
