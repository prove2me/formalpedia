-- Prove2me | Theorems.Thm_Groundwork_PolyT_mod
-- name    : Groundwork.PolyT.mod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:23.78879+00:00
-- url     : https://prove2.me/theorems/36ba290f-d49c-4cec-af24-d7914ef8e8f6
-- title:
--   Poly T: mod
-- statement:
--   The remainder is polynomial-time; the divisor 0 is a separate case (the remainder is then the
--   number itself).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L158-L166
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L158-L166

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

theorem Groundwork.PolyT.mod {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x % g x) := by sorry
