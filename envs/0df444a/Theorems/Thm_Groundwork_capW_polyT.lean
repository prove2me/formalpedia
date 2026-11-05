-- Prove2me | Theorems.Thm_Groundwork_capW_polyT
-- name    : Groundwork.capW_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:29:42.737945+00:00
-- url     : https://prove2.me/theorems/4c5bf85f-f200-414f-9f73-64fa979b0b03
-- title:
--   Groundwork: cap W poly T
-- statement:
--   The length of the bit string of a label when the bound c on the number of symbols is a number in
--   binary that is at most
--   the length n, which is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Digits.lean#L47-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Digits.lean#L47-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_ToTuring_Poly_Digits
set_option autoImplicit false
section
section
open Groundwork
variable {α : Type} [Enc α]

theorem Groundwork.capW_polyT {n c : α → ℕ} (hn : Unary n) (hc : PolyT c) (h : ∀ a, c a ≤ n a) :
    PolyT fun a => Prog.capW (n a) (c a) := by sorry
