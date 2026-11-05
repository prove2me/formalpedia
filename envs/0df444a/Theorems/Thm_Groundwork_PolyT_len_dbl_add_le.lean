-- Prove2me | Theorems.Thm_Groundwork_PolyT_len_dbl_add_le
-- name    : Groundwork.PolyT.len_dbl_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:59.515744+00:00
-- url     : https://prove2.me/theorems/3661f35e-75f4-4701-9837-0b06cae41326
-- title:
--   Poly T: len dbl add le
-- statement:
--   The word of c + c + z is longer than those of c and z together by at most 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L25-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L25-L35

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

theorem Groundwork.PolyT.len_dbl_add_le (c z : ℕ) : len (c + c + z) ≤ len c + len z + 4 := by sorry
