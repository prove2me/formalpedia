-- Prove2me | Theorems.Thm_Groundwork_PolyT_foldr_bits_mul
-- name    : Groundwork.PolyT.foldr_bits_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:15.026781+00:00
-- url     : https://prove2.me/theorems/48a3a482-23f4-4683-a2ee-a822784043b0
-- title:
--   Poly T: foldr bits mul
-- statement:
--   The product, read off the binary digits of the second factor from the top: double, and add m if
--   the digit is 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L59-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L59-L65

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

theorem Groundwork.PolyT.foldr_bits_mul (m n : ℕ) :
    (Nat.bits n).foldr (fun b acc => acc + acc + bif b then m else 0) 0 = m * n := by sorry
