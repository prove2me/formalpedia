-- Prove2me | Theorems.Thm_Groundwork_PolyT_foldr_bits_divStep
-- name    : Groundwork.PolyT.foldr_bits_divStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:09.888942+00:00
-- url     : https://prove2.me/theorems/39176f2b-58ff-4940-a945-a0061686f8e1
-- title:
--   Poly T: foldr bits div Step
-- statement:
--   The rounds over all digits of n, from the top, give quotient and remainder of n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L116-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L116-L121

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

theorem Groundwork.PolyT.foldr_bits_divStep {d : ℕ} (hd : 0 < d) (n : ℕ) :
    (Nat.bits n).foldr (fun b s => divStep d s b) (0, 0) = (n / d, n % d) := by sorry
