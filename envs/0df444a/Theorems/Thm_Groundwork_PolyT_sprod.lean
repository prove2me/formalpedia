-- Prove2me | Theorems.Thm_Groundwork_PolyT_sprod
-- name    : Groundwork.PolyT.sprod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:27:42.639344+00:00
-- url     : https://prove2.me/theorems/0a8c3684-894f-4614-a955-db5d78b89970
-- title:
--   Poly T: sprod
-- statement:
--   The product of two lists in the notation ×ˢ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L98-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L98-L100

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

theorem Groundwork.PolyT.sprod {l : α → List β} {l' : α → List γ} (hl : PolyT l) (hl' : PolyT l') :
    PolyT (fun x => l x ×ˢ l' x) := by sorry
