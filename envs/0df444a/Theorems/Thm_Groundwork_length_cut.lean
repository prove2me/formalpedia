-- Prove2me | Theorems.Thm_Groundwork_length_cut
-- name    : Groundwork.length_cut
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:17.61455+00:00
-- url     : https://prove2.me/theorems/bfa23168-4b7b-4ee4-bb54-d8208aa6e8d2
-- title:
--   Groundwork: length cut
-- statement:
--   The Groundwork construction uses the length cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L141-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L141-L150

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

theorem Groundwork.length_cut (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool) (hw : w.length = (e.map c).sum)
    {i : ι} (h : i ∈ e) : (cut c d e w i).length = c i := by sorry
