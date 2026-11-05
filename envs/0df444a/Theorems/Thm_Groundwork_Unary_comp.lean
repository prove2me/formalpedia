-- Prove2me | Theorems.Thm_Groundwork_Unary_comp
-- name    : Groundwork.Unary.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:27:55.30647+00:00
-- url     : https://prove2.me/theorems/62b56cdf-01aa-4259-ad62-e912b7665af0
-- title:
--   Unary: comp
-- statement:
--   The Unary construction uses the comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L40-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L40-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
attribute [local fun_prop] Groundwork.PolyT.comp


set_option autoImplicit false
section
section
open Groundwork Groundwork.Unary
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
variable {f g : α → ℕ}

theorem Groundwork.Unary.comp (hf : Unary f) {h : β → α} (hh : PolyT h) :
    Unary fun b => f (h b) := by sorry
