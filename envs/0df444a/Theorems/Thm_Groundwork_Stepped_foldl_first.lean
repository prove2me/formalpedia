-- Prove2me | Theorems.Thm_Groundwork_Stepped_foldl_first
-- name    : Groundwork.Stepped.foldl_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:18.081736+00:00
-- url     : https://prove2.me/theorems/94f00bc1-3c46-480c-a091-e27877c27b16
-- title:
--   Stepped: foldl first
-- statement:
--   The Stepped construction uses the foldl first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L178-L187
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L178-L187

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Stepped
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Range
import Definitions.Def_StepMachines_Prog_Range
set_option autoImplicit false
section
open Groundwork Groundwork.Stepped
open Finset
variable {α β γ : Type}

theorem Groundwork.Stepped.foldl_first (q : ℕ → Bool) (k : ℕ) :
    (List.range k).foldl (fun c y => match c with | some i => some i | none => if q y then some y else none)
      none = (List.range k).find? q := by sorry
