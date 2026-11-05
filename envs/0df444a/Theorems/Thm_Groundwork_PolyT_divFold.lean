-- Prove2me | Theorems.Thm_Groundwork_PolyT_divFold
-- name    : Groundwork.PolyT.divFold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:16.250997+00:00
-- url     : https://prove2.me/theorems/bd167ee6-4091-46a6-bc23-64ef14d37bc7
-- title:
--   Poly T: div Fold
-- statement:
--   Quotient and remainder together, as one fold.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L139-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L139-L143

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

theorem Groundwork.PolyT.divFold {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => (Nat.bits (f x)).reverse.foldl (divStep (g x)) (0, 0)) := by sorry
