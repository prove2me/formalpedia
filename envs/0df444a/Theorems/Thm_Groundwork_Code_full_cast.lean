-- Prove2me | Theorems.Thm_Groundwork_Code_full_cast
-- name    : Groundwork.Code.full_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:33:36.685011+00:00
-- url     : https://prove2.me/theorems/cc326b52-e4ac-4297-88d5-86243c6312ea
-- title:
--   Code: full cast
-- statement:
--   The Code construction uses the full cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Code.lean#L116-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Code.lean#L116-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Net
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_StepMachines_Math_Code
set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}

theorem Groundwork.Code.full_cast (c : Code S n) {S' : Finset X} {n' : ℕ} (hS : S = S') (hn : n = n') (h : c.Full) :
    (c.cast hS hn).Full := by sorry
