-- Prove2me | Theorems.Thm_Groundwork_length_glue
-- name    : Groundwork.length_glue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:04.973387+00:00
-- url     : https://prove2.me/theorems/e6aa4763-a22b-44ca-ad61-cfc054828426
-- title:
--   Groundwork: length glue
-- statement:
--   The Groundwork construction uses the length glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L183-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L183-L190

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
omit [DecidableEq ι]

theorem Groundwork.length_glue (c : ι → ℕ) (e : List ι) (t : ι → List Bool) (h : ∀ i ∈ e, (t i).length = c i) :
    (glue e t).length = (e.map c).sum := by sorry
