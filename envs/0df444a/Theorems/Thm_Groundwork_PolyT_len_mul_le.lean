-- Prove2me | Theorems.Thm_Groundwork_PolyT_len_mul_le
-- name    : Groundwork.PolyT.len_mul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:38:58.711409+00:00
-- url     : https://prove2.me/theorems/07dea3b2-e1c5-40d5-8e11-d06b605bf5c9
-- title:
--   Poly T: len mul le
-- statement:
--   The word of a product is at most as long as the words of the factors together.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L48-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L48-L53

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

theorem Groundwork.PolyT.len_mul_le (a b : ℕ) : len (a * b) ≤ len a + len b := by sorry
