-- Prove2me | Theorems.Thm_Groundwork_PolyT_dedup
-- name    : Groundwork.PolyT.dedup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:27:02.096836+00:00
-- url     : https://prove2.me/theorems/ea34ec87-1d62-4ad8-b19d-c4dc3a689777
-- title:
--   Poly T: dedup
-- statement:
--   Removal of duplicates: a fold from the right that adds an element unless the result already has
--   it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L43-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L43-L63

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

theorem Groundwork.PolyT.dedup [DecidableEq β] [EqT β] {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).dedup) := by sorry
