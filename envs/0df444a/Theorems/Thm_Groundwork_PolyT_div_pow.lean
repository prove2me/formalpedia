-- Prove2me | Theorems.Thm_Groundwork_PolyT_div_pow
-- name    : Groundwork.PolyT.div_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:38:53.86966+00:00
-- url     : https://prove2.me/theorems/19d958f1-e28a-407e-b7c9-77ecfa0c63d1
-- title:
--   Poly T: div pow
-- statement:
--   a / b ^ q is polynomial-time with all three numbers in binary: the exponent is first cut off at
--   the number of binary
--   digits of a, which can be written in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L256-L260
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L256-L260

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

theorem Groundwork.PolyT.div_pow {a b q : α → ℕ} (ha : PolyT a) (hb : PolyT b) (hq : PolyT q) :
    PolyT (fun x => a x / b x ^ q x) := by sorry
