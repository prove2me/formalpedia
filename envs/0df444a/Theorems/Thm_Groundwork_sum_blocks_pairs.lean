-- Prove2me | Theorems.Thm_Groundwork_sum_blocks_pairs
-- name    : Groundwork.sum_blocks_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:22.7847+00:00
-- url     : https://prove2.me/theorems/4ffecbc9-e15a-4a8b-bdd2-59c9f728a9a9
-- title:
--   Groundwork: sum blocks pairs
-- statement:
--   A sum over all words of K(K-1)/2 · ℓ bits is a sum over all labellings of the pairs a < b in Fin
--   K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L369-L381
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Chunks.lean#L369-L381

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

theorem Groundwork.sum_blocks_pairs {X : Type*} [AddCommMonoid X] (K ℓ : ℕ) (d : List Bool)
    (F : (Fin K × Fin K → List Bool) → X) :
    ∑ w ∈ words (K * (K - 1) / 2 * ℓ), F (fun p => if p.1 < p.2 then block ℓ (tri p.1 p.2) w else d)
      = ∑ t ∈ tuples (fun p : Fin K × Fin K => p.1 < p.2) (fun _ => words ℓ) d, F t := by sorry
