-- Prove2me | Theorems.Thm_Groundwork_PolyT_optionElim
-- name    : Groundwork.PolyT.optionElim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:47:31.547643+00:00
-- url     : https://prove2.me/theorems/81729d0b-a3a9-44df-8408-09a9f5b85bcf
-- title:
--   Poly T: option Elim
-- statement:
--   Case distinction on an option o x; both branches see the context x.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L176-L183
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L176-L183

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

theorem Groundwork.PolyT.optionElim {o : α → Option β} {d : α → γ} {f : α → β → γ} (ho : PolyT o) (hd : PolyT d)
    (hf : PolyT fun p : α × β => f p.1 p.2) : PolyT (fun x => (o x).elim (d x) (f x)) := by sorry
