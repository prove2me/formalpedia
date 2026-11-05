-- Prove2me | Theorems.Thm_Groundwork_Sparsify_toFinset_redL
-- name    : Groundwork.Sparsify.toFinset_redL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:23:09.950259+00:00
-- url     : https://prove2.me/theorems/fb90f816-a52c-45c1-be10-47c3beb9700d
-- title:
--   Sparsify: to Finset red L
-- statement:
--   The Sparsify construction uses the to Finset red L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyStep.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyStep.lean#L35-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Sparsify
import Definitions.Def_StepMachines_Math_SparsifyTree
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_StepMachines_Math_SparsifyStep
set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {α : Type*} [DecidableEq α]

theorem Groundwork.Sparsify.toFinset_redL (s : List (Finset α)) : (redL s).toFinset = red s.toFinset := by sorry
