-- Prove2me | Theorems.Thm_Groundwork_TM_Run_one
-- name    : Groundwork.TM.Run.one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:18:51.635204+00:00
-- url     : https://prove2.me/theorems/f2c7bd55-b2e8-4c0a-bdf5-10414721a341
-- title:
--   Run: one
-- statement:
--   The Run construction uses the one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean#L27-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean#L27-L27

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ToTuring_TM_Run
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing

theorem Groundwork.TM.Run.one {C : Type} {f : C → Option C} {a b : C} (h : f a = some b) : Run f a 1 b := by sorry
