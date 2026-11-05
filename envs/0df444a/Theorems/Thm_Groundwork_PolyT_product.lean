-- Prove2me | Theorems.Thm_Groundwork_PolyT_product
-- name    : Groundwork.PolyT.product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:27:25.651947+00:00
-- url     : https://prove2.me/theorems/60b3b4f0-1f80-470f-9772-8b7019a997a6
-- title:
--   Poly T: product
-- statement:
--   The list of all pairs of an element of the first list and an element of the second.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L92-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L92-L95

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

theorem Groundwork.PolyT.product {l : α → List β} {l' : α → List γ} (hl : PolyT l) (hl' : PolyT l') :
    PolyT (fun x => (l x).product (l' x)) := by sorry
