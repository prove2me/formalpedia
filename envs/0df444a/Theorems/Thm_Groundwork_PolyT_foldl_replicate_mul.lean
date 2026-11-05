-- Prove2me | Theorems.Thm_Groundwork_PolyT_foldl_replicate_mul
-- name    : Groundwork.PolyT.foldl_replicate_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:40:11.226689+00:00
-- url     : https://prove2.me/theorems/d376a3b8-c439-4158-a6f0-f7ccda6b4aa9
-- title:
--   Poly T: foldl replicate mul
-- statement:
--   Multiplying n times by b multiplies by b ^ n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L178-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L178-L182

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

theorem Groundwork.PolyT.foldl_replicate_mul (b n a : ℕ) :
    (List.replicate n ()).foldl (fun acc _ => acc * b) a = a * b ^ n := by sorry
