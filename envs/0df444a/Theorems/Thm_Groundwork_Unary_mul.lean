-- Prove2me | Theorems.Thm_Groundwork_Unary_mul
-- name    : Groundwork.Unary.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:28:16.176758+00:00
-- url     : https://prove2.me/theorems/72aa2a4c-02e9-45be-bf27-c980d880dd57
-- title:
--   Unary: mul
-- statement:
--   The Unary construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L48-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L48-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Theorems.Thm_Groundwork_PB_mul
import Theorems.Thm_Groundwork_PolyT_mul
attribute [local fun_prop] Groundwork.PolyT.mul


set_option autoImplicit false
section
section
open Groundwork Groundwork.Unary
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
variable {f g : α → ℕ}

theorem Groundwork.Unary.mul (hf : Unary f) (hg : Unary g) :
    Unary fun c => f c * g c := by sorry
