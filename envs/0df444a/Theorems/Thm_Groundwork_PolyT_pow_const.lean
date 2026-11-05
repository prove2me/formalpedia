-- Prove2me | Theorems.Thm_Groundwork_PolyT_pow_const
-- name    : Groundwork.PolyT.pow_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:18.246829+00:00
-- url     : https://prove2.me/theorems/4df96fad-2da4-4a3f-9672-28c11422989f
-- title:
--   Poly T: pow const
-- statement:
--   A power with a fixed exponent is polynomial-time: k products.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L171-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L171-L175

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

theorem Groundwork.PolyT.pow_const {f : α → ℕ} (hf : PolyT f) (k : ℕ) :
    PolyT (fun x => f x ^ k) := by sorry
