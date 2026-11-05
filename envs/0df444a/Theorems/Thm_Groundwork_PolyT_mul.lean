-- Prove2me | Theorems.Thm_Groundwork_PolyT_mul
-- name    : Groundwork.PolyT.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:38:51.684867+00:00
-- url     : https://prove2.me/theorems/aa434ad2-ac7c-48df-a9dd-bea8b5ecdac5
-- title:
--   Poly T: mul
-- statement:
--   The product of two numbers in binary is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L68-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L68-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Theorems.Thm_Groundwork_PB_mul

set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.mul {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x * g x) := by sorry
