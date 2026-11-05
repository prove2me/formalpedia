-- Prove2me | Theorems.Thm_Groundwork_getD_chunks_replicate
-- name    : Groundwork.getD_chunks_replicate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:16.041196+00:00
-- url     : https://prove2.me/theorems/176ddf6d-30d9-440b-bf61-274462b82017
-- title:
--   Groundwork: get D chunks replicate
-- statement:
--   The Groundwork construction uses the get D chunks replicate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L262-L272
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L262-L272

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_StepMachines_Prog_Chunks
set_option autoImplicit false
section
open Groundwork
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem Groundwork.getD_chunks_replicate (ℓ r j : ℕ) (w d : List Bool) (hj : j < r) :
    (chunks (List.replicate r ℓ) w).getD j d = block ℓ j w := by sorry
