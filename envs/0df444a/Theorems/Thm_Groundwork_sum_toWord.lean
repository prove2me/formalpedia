-- Prove2me | Theorems.Thm_Groundwork_sum_toWord
-- name    : Groundwork.sum_toWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:26:52.629616+00:00
-- url     : https://prove2.me/theorems/d4de9a1a-2c49-4130-b8af-d79326622843
-- title:
--   Groundwork: sum to Word
-- statement:
--   A sum over the counter y < 2^ℓ is a sum over all words of length ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L87-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L87-L89

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

theorem Groundwork.sum_toWord {X : Type*} [AddCommMonoid X] (ℓ : ℕ) (G : List Bool → X) :
    ∑ y ∈ range (2 ^ ℓ), G (toWord ℓ y) = ∑ w ∈ words ℓ, G w := by sorry
