-- Prove2me | Theorems.Thm_Groundwork_TM_upd4_t2
-- name    : Groundwork.TM.upd4_t2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:04.662542+00:00
-- url     : https://prove2.me/theorems/d27d6e18-571b-423f-84a5-89a2697ad956
-- title:
--   TM: upd4 t2
-- statement:
--   The TM construction uses the upd4 t2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L103-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L103-L104

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Rename
import Definitions.Def_ToTuring_TM_Stacks
import Definitions.Def_ToTuring_TM_Move
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable (A B₁ B₂ C W : List Sym)

theorem Groundwork.TM.upd4_t2 : Function.update (st4 A B₁ B₂ C) .t2 W = st4 A B₁ W C := by sorry
