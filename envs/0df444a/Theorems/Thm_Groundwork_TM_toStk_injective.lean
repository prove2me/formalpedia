-- Prove2me | Theorems.Thm_Groundwork_TM_toStk_injective
-- name    : Groundwork.TM.toStk_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:59.036626+00:00
-- url     : https://prove2.me/theorems/3240a0ed-2c2c-404e-bd46-c379b48bed77
-- title:
--   TM: to Stk injective
-- statement:
--   The TM construction uses the to Stk injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L202-L211
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Move.lean#L202-L211

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

theorem Groundwork.TM.toStk_injective {i j k : Stk} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : i ≠ .cnt) (hj : j ≠ .cnt)
    (hk : k ≠ .cnt) : Function.Injective (toStk i j k) := by sorry
