-- Prove2me | Theorems.Thm_Groundwork_PolyT_sumCore
-- name    : Groundwork.PolyT.sumCore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:51:42.102222+00:00
-- url     : https://prove2.me/theorems/95b82435-2a3c-4daa-9d43-a594ed01d36c
-- title:
--   Poly T: sum Core
-- statement:
--   Case distinction on a sum, without context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L48-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Cases.lean#L48-L88

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

theorem Groundwork.PolyT.sumCore {f : β → δ} {g : γ → δ} (hf : PolyT f) (hg : PolyT g) : PolyT (fun s : β ⊕ γ => s.elim f g) := by sorry
