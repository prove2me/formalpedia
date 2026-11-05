-- Prove2me | Theorems.Thm_Groundwork_TM_Run_iterate
-- name    : Groundwork.TM.Run.iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:07.882341+00:00
-- url     : https://prove2.me/theorems/4a47a791-343b-4ad7-bb96-5af6f78b9747
-- title:
--   Run: iterate
-- statement:
--   The same in Mathlib's form (`StateTransition.EvalsTo`): n iterations of `flip bind f` lead from
--   `some a` to `some b`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean#L37-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean#L37-L42

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

theorem Groundwork.TM.Run.iterate {C : Type} {f : C → Option C} : ∀ {n : ℕ} {a b : C}, Run f a n b → (flip bind f)^[n] (some a) = some b
  := by sorry
