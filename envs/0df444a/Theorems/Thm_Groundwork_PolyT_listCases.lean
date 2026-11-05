-- Prove2me | Theorems.Thm_Groundwork_PolyT_listCases
-- name    : Groundwork.PolyT.listCases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:50:49.042336+00:00
-- url     : https://prove2.me/theorems/3ff7bb77-8906-496e-8e9e-2a4e164ba9f6
-- title:
--   Poly T: list Cases
-- statement:
--   Case distinction on a list l x: it is empty, or it has a first element and a rest; both branches
--   see the context x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L170-L174
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L170-L174

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Closure_Cases
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Turing
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.listCases {l : α → List β} {d : α → γ} {f : α → β → List β → γ} (hl : PolyT l) (hd : PolyT d)
    (hf : PolyT fun p : α × β × List β => f p.1 p.2.1 p.2.2) :
    PolyT (fun x => match l x with | [] => d x | e :: r => f x e r) := by sorry
