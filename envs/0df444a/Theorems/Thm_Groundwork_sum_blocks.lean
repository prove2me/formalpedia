-- Prove2me | Theorems.Thm_Groundwork_sum_blocks
-- name    : Groundwork.sum_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:36.060654+00:00
-- url     : https://prove2.me/theorems/3fe34b7a-33e5-4954-b6d5-77fb79f36937
-- title:
--   Groundwork: sum blocks
-- statement:
--   A sum over all words of r·ℓ bits of F(the blocks) is the sum of F over all tuples of words of ℓ
--   bits.
--   pos numbers the indices i with P i by 0, …, r-1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L277-L314
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L277-L314

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

theorem Groundwork.sum_blocks {X : Type*} [AddCommMonoid X] [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (pos : ι → ℕ) (r ℓ : ℕ) (hinj : ∀ i i', P i → P i' → pos i = pos i' → i = i') (hlt : ∀ i, P i → pos i < r)
    (hsurj : ∀ j < r, ∃ i, P i ∧ pos i = j) (d : List Bool) (F : (ι → List Bool) → X) :
    ∑ w ∈ words (r * ℓ), F (fun i => if P i then block ℓ (pos i) w else d)
      = ∑ t ∈ tuples P (fun _ => words ℓ) d, F t := by sorry
