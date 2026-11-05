-- Prove2me | Theorems.Thm_Groundwork_capW_unary
-- name    : Groundwork.capW_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:19:20.319011+00:00
-- url     : https://prove2.me/theorems/3dd2b15b-4167-4e00-a9bf-270473e8b68d
-- title:
--   Groundwork: cap W unary
-- statement:
--   The Groundwork construction uses the cap W unary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Digits.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Digits.lean#L41-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_ToTuring_Poly_Digits
set_option autoImplicit false
section
section
open Groundwork
variable {α : Type} [Enc α]

theorem Groundwork.capW_unary {n c : α → ℕ} (hn : Unary n) (hc : Unary c) : Unary fun a => Prog.capW (n a) (c a) := by sorry
