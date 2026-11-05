-- Prove2me | Theorems.Thm_Groundwork_tb_polyT
-- name    : Groundwork.tb_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:19:38.035197+00:00
-- url     : https://prove2.me/theorems/3d0e45ef-bdd4-4769-8936-c7fb51b6eb7d
-- title:
--   Groundwork: tb poly T
-- statement:
--   The Groundwork construction uses the tb poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Digits.lean#L34-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Digits.lean#L34-L36

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

theorem Groundwork.tb_polyT {f : α → ℕ} (hf : Unary f) : PolyT fun a => Prog.tb (f a) := by sorry
