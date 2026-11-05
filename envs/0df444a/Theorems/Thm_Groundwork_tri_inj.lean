-- Prove2me | Theorems.Thm_Groundwork_tri_inj
-- name    : Groundwork.tri_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:55.976068+00:00
-- url     : https://prove2.me/theorems/b27ad5e2-1884-4857-af5d-b0922422b8d4
-- title:
--   Groundwork: tri inj
-- statement:
--   The Groundwork construction uses the tri inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L343-L353
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L343-L353

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

theorem Groundwork.tri_inj {a b a' b' : ℕ} (hab : a < b) (hab' : a' < b') (h : tri a b = tri a' b') :
    a = a' ∧ b = b' := by sorry
