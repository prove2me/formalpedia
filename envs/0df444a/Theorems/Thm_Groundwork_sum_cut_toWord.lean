-- Prove2me | Theorems.Thm_Groundwork_sum_cut_toWord
-- name    : Groundwork.sum_cut_toWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:15.76693+00:00
-- url     : https://prove2.me/theorems/a66011c7-009f-48d9-85b9-0fd85daef363
-- title:
--   Groundwork: sum cut to Word
-- statement:
--   sum_toWord followed by sum_cut: a sum over the counter y < 2^(Σ c i) of F(the chunks of the word
--   of y) is the sum
--   of F over all tuples of words.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L245-L250
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L245-L250

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

theorem Groundwork.sum_cut_toWord {X : Type*} [AddCommMonoid X] [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (e : List ι) (he : e.Nodup) (hP : ∀ i, i ∈ e ↔ P i) (c : ι → ℕ) (d : List Bool)
    (F : (ι → List Bool) → X) :
    ∑ y ∈ range (2 ^ (e.map c).sum), F (cut c d e (toWord (e.map c).sum y))
      = ∑ t ∈ tuples P (fun i => words (c i)) d, F t := by sorry
