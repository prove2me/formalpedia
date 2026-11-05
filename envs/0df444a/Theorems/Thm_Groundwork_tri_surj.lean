-- Prove2me | Theorems.Thm_Groundwork_tri_surj
-- name    : Groundwork.tri_surj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:05.073587+00:00
-- url     : https://prove2.me/theorems/ba3a3632-d5c4-43fd-81cf-7a18a791b344
-- title:
--   Groundwork: tri surj
-- statement:
--   The Groundwork construction uses the tri surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L355-L365
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L355-L365

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

theorem Groundwork.tri_surj {K j : ℕ} (h : j < K * (K - 1) / 2) : ∃ a b, a < b ∧ b < K ∧ tri a b = j := by sorry
