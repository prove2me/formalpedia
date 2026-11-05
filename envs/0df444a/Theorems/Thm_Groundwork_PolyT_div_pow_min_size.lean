-- Prove2me | Theorems.Thm_Groundwork_PolyT_div_pow_min_size
-- name    : Groundwork.PolyT.div_pow_min_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:38.86978+00:00
-- url     : https://prove2.me/theorems/b66ddab7-9e38-46c3-ae9a-9f952afdcdff
-- title:
--   Poly T: div pow min size
-- statement:
--   In a / b ^ q the exponent may be cut off at the number of binary digits of a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L238-L251
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L238-L251

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

theorem Groundwork.PolyT.div_pow_min_size (a b q : ℕ) : a / b ^ min q (Nat.size a) = a / b ^ q := by sorry
