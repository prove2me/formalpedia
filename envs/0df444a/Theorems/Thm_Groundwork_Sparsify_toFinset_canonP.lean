-- Prove2me | Theorems.Thm_Groundwork_Sparsify_toFinset_canonP
-- name    : Groundwork.Sparsify.toFinset_canonP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:20.337287+00:00
-- url     : https://prove2.me/theorems/f97cdc5a-883b-4074-a22b-c3716e4cebd0
-- title:
--   Sparsify: to Finset canon P
-- statement:
--   The Sparsify construction uses the to Finset canon P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyProg.lean#L123-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyProg.lean#L123-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyList
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup
import Definitions.Def_StepMachines_Math_SparsifyProg
set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {τ n : ℕ} {ψ s l h : PFml} {p q : ℕ}

theorem Groundwork.Sparsify.toFinset_canonP {C : PCl} (hC : C ∈ ψ) : (canonP (litsOf ψ) C).toFinset = C.toFinset := by sorry
