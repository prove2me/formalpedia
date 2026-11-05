-- Prove2me | Theorems.Thm_Groundwork_cut_eq_getD_beq
-- name    : Groundwork.cut_eq_getD_beq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:27.678137+00:00
-- url     : https://prove2.me/theorems/197d7033-6697-40ae-ac1c-1eca29ae0cad
-- title:
--   Groundwork: cut eq get D beq
-- statement:
--   cut_eq_getD for any lawful ==, such as the one of a product type.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L123-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L123-L131

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

theorem Groundwork.cut_eq_getD_beq [BEq ι] [LawfulBEq ι] (c : ι → ℕ) (d : List Bool) (e : List ι) (w : List Bool)
    (i : ι) : cut c d e w i = (chunks (e.map c) w).getD (e.idxOf i) d := by sorry
