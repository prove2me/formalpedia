-- Prove2me | Theorems.Thm_Groundwork_Unary_of_le
-- name    : Groundwork.Unary.of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:28:43.773432+00:00
-- url     : https://prove2.me/theorems/ddbee951-96f6-4f33-8439-d7bd613463a4
-- title:
--   Unary: of le
-- statement:
--   A polynomial-time number bounded by a unary one is itself unary: cut the list of length `g c`
--   down to length `f c`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L56-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L56-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
set_option autoImplicit false
section
section
open Groundwork Groundwork.Unary
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
variable {f g : α → ℕ}

theorem Groundwork.Unary.of_le (hg : Unary g) (hf : PolyT f) (h : ∀ c, f c ≤ g c) :
    Unary f := by sorry
