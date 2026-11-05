-- Prove2me | Theorems.Thm_Groundwork_TM_Run_trans
-- name    : Groundwork.TM.Run.trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:16:42.863635+00:00
-- url     : https://prove2.me/theorems/120b713d-0430-48d4-9387-3eae0a422967
-- title:
--   Run: trans
-- statement:
--   The Run construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean#L29-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean#L29-L33

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

theorem Groundwork.TM.Run.trans {C : Type} {f : C → Option C} : ∀ {m : ℕ} {a b c : C} {n : ℕ}, Run f a m b → Run f b n c → Run f a (m + n) c
  := by sorry
