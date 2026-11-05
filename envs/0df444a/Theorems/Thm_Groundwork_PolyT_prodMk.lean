-- Prove2me | Theorems.Thm_Groundwork_PolyT_prodMk
-- name    : Groundwork.PolyT.prodMk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:28.462227+00:00
-- url     : https://prove2.me/theorems/85f5d9b7-06a8-45d6-8d1e-84c216a74813
-- title:
--   Poly T: prod Mk
-- statement:
--   Duplicate x; f on the copy on top; exchange; g on x, now on top; exchange; make the pair.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L69-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L69-L87

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.prodMk {f : α → β} {g : α → γ} (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => (f x, g x)) := by sorry
