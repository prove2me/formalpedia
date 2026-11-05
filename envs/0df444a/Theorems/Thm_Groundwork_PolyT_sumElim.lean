-- Prove2me | Theorems.Thm_Groundwork_PolyT_sumElim
-- name    : Groundwork.PolyT.sumElim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:47:36.981413+00:00
-- url     : https://prove2.me/theorems/3672536b-129a-4d8b-9046-27215f8d31cc
-- title:
--   Poly T: sum Elim
-- statement:
--   Case distinction on a sum s x; each branch sees the context x and what lies under the tag.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L157-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L157-L167

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
import Theorems.Thm_Groundwork_PolyT_elim

set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.sumElim {s : α → β ⊕ γ} {f : α → β → δ} {g : α → γ → δ} (hs : PolyT s)
    (hf : PolyT fun p : α × β => f p.1 p.2) (hg : PolyT fun p : α × γ => g p.1 p.2) :
    PolyT (fun x => (s x).elim (f x) (g x)) := by sorry
