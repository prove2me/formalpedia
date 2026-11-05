-- Prove2me | Theorems.Thm_Groundwork_PolyT_comp
-- name    : Groundwork.PolyT.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:20.876581+00:00
-- url     : https://prove2.me/theorems/e1e412e0-48e2-4f2b-88ad-896e5a3e30c0
-- title:
--   Poly T: comp
-- statement:
--   Run the fragment of g, then that of f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L61-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L61-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
import Theorems.Thm_Groundwork_PB_comp

set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.comp {f : β → γ} {g : α → β} (hf : PolyT f) (hg : PolyT g) : PolyT (fun x => f (g x)) := by sorry
