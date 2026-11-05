-- Prove2me | Theorems.Thm_Groundwork_PolyT_len_divStep_le
-- name    : Groundwork.PolyT.len_divStep_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:13.266977+00:00
-- url     : https://prove2.me/theorems/efd5c958-4797-411d-a4e5-389c64849d2c
-- title:
--   Poly T: len div Step le
-- statement:
--   A round makes the word of the pair longer by at most 6.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L124-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L124-L136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.len_divStep_le (d : ℕ) (s : ℕ × ℕ) (b : Bool) : len (divStep d s b) ≤ len s + 6 := by sorry
