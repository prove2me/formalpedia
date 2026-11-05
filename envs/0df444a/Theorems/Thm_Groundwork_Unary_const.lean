-- Prove2me | Theorems.Thm_Groundwork_Unary_const
-- name    : Groundwork.Unary.const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:27:48.375171+00:00
-- url     : https://prove2.me/theorems/7603cb5f-f697-4f0e-a041-9ccf8686512b
-- title:
--   Unary: const
-- statement:
--   The Unary construction uses the const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L36-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L36-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
attribute [local fun_prop] Groundwork.PolyT.const


set_option autoImplicit false
section
section
open Groundwork Groundwork.Unary
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
variable {f g : α → ℕ}

theorem Groundwork.Unary.const (n : ℕ) :
    Unary fun _ : α => n := by sorry
