-- Prove2me | Theorems.Thm_Groundwork_PolyT_decide_mem
-- name    : Groundwork.PolyT.decide_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:27:46.481856+00:00
-- url     : https://prove2.me/theorems/b71bd963-0cef-4821-a056-e7b8579b68d6
-- title:
--   Poly T: decide mem
-- statement:
--   Membership in the form `decide (b ∈ l)`. `BEq` and `LawfulBEq` are needed because the instance
--   `Decidable (b ∈ l)` of Lean's
--   core library is built from them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L37-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L37-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.ProdSigma
import Definitions.Def_ToTuring_Lib_List3
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.decide_mem [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {b : α → β} {l : α → List β} (hb : PolyT b)
    (hl : PolyT l) : PolyT (fun x => decide (b x ∈ l x)) := by sorry
