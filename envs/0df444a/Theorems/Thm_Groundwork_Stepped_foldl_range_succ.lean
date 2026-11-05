-- Prove2me | Theorems.Thm_Groundwork_Stepped_foldl_range_succ
-- name    : Groundwork.Stepped.foldl_range_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:34.234093+00:00
-- url     : https://prove2.me/theorems/d29ebd4b-f36b-475b-92d2-f53df5466ce9
-- title:
--   Stepped: foldl range succ
-- statement:
--   The Stepped construction uses the foldl range succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L49-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Range.lean#L49-L51

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

theorem Groundwork.Stepped.foldl_range_succ (f : γ → ℕ → γ) (c : γ) (k : ℕ) :
    (List.range (k + 1)).foldl f c = f ((List.range k).foldl f c) k := by sorry
