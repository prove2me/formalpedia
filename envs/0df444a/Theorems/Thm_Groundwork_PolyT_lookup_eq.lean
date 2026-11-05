-- Prove2me | Theorems.Thm_Groundwork_PolyT_lookup_eq
-- name    : Groundwork.PolyT.lookup_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:27:20.102182+00:00
-- url     : https://prove2.me/theorems/be02ab13-b29d-4a60-bc48-6e3265d2983a
-- title:
--   Poly T: lookup eq
-- statement:
--   On the elements of the list the table gives F.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L31-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Table.lean#L31-L38

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
omit [Enc β] [Enc γ]

theorem Groundwork.PolyT.lookup_eq [DecidableEq β] (F : β → γ) (d : γ) {l : List β} {y : β} (h : y ∈ l) : lookup F d l y = F y := by sorry
