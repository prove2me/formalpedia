-- Prove2me | Theorems.Thm_Groundwork_PolyT_len_bound_mem
-- name    : Groundwork.PolyT.len_bound_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:34:54.441526+00:00
-- url     : https://prove2.me/theorems/7484648e-bd0a-49fe-98e2-0ad420f1a793
-- title:
--   Poly T: len bound mem
-- statement:
--   A function of the context and of a member of a polynomial-time list has values of polynomial
--   length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean#L27-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean#L27-L35

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

theorem Groundwork.PolyT.len_bound_mem {f : α → β → γ} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    ∃ b, PB b ∧ ∀ x, ∀ e ∈ l x, len (f x e) ≤ b (len x) := by sorry
