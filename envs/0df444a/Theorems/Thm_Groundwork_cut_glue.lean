-- Prove2me | Theorems.Thm_Groundwork_cut_glue
-- name    : Groundwork.cut_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:14.706632+00:00
-- url     : https://prove2.me/theorems/b05c73f4-3b0b-4edb-9544-e31f568ec1f0
-- title:
--   Groundwork: cut glue
-- statement:
--   The Groundwork construction uses the cut glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L192-L212
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L192-L212

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

theorem Groundwork.cut_glue (c : ι → ℕ) (d : List Bool) (e : List ι) (he : e.Nodup) (t : ι → List Bool)
    (h : ∀ i ∈ e, (t i).length = c i) (h' : ∀ i, i ∉ e → t i = d) : cut c d e (glue e t) = t := by sorry
