-- Prove2me | Theorems.Thm_Groundwork_PolyT_testBit
-- name    : Groundwork.PolyT.testBit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:31.658616+00:00
-- url     : https://prove2.me/theorems/2144dbf6-6a46-4e6c-8bde-4f1a58478bf7
-- title:
--   Poly T: test Bit
-- statement:
--   Bit number `g x` of `f x`: a fold over the binary digits that carries the position and the bit
--   found so far.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L107-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L107-L121

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1
import Definitions.Def_ToTuring_Lib_Nat1b
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.testBit {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => (f x).testBit (g x)) := by sorry
