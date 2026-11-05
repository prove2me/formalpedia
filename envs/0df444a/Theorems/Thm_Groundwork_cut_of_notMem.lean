-- Prove2me | Theorems.Thm_Groundwork_cut_of_notMem
-- name    : Groundwork.cut_of_notMem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:33.3372+00:00
-- url     : https://prove2.me/theorems/52b35b2d-4d17-456e-9946-c4919ebabeb6
-- title:
--   Groundwork: cut of not Mem
-- statement:
--   The Groundwork construction uses the cut of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L133-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L133-L139

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

theorem Groundwork.cut_of_notMem (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool) {i : ι} (h : i ∉ e) :
    cut c d e w i = d := by sorry
