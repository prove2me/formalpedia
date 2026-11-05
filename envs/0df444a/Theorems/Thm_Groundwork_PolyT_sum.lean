-- Prove2me | Theorems.Thm_Groundwork_PolyT_sum
-- name    : Groundwork.PolyT.sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:18.79019+00:00
-- url     : https://prove2.me/theorems/fa16ce1b-b0dd-4c60-bce5-d5266ad8b243
-- title:
--   Poly T: sum
-- statement:
--   The sum of a list of numbers: a fold that adds the elements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L124-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L124-L138

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1
import Definitions.Def_ToTuring_Lib_Nat1b
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.sum {l : α → List ℕ} (hl : PolyT l) :
    PolyT (fun x => (l x).sum) := by sorry
