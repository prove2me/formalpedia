-- Prove2me | Theorems.Thm_Groundwork_PolyT_foldr_add
-- name    : Groundwork.PolyT.foldr_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:34:44.807402+00:00
-- url     : https://prove2.me/theorems/15a0a892-d22d-41e2-936d-1f7b879c6ba4
-- title:
--   Poly T: foldr add
-- statement:
--   The fold from the right when every step adds at most b(len x) to the length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean#L84-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean#L84-L95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.foldr_add {l : α → List ε} {a : α → γ} {g : α → ε → γ → γ} (hl : PolyT l) (ha : PolyT a)
    (hg : PolyT fun p : α × ε × γ => g p.1 p.2.1 p.2.2)
    (hB : ∃ b, PB b ∧ ∀ x c, ∀ e ∈ l x, len (g x e c) ≤ len c + b (len x)) :
    PolyT (fun x => (l x).foldr (g x) (a x)) := by sorry
