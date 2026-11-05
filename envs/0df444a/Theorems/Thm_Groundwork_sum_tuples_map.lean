-- Prove2me | Theorems.Thm_Groundwork_sum_tuples_map
-- name    : Groundwork.sum_tuples_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:45.008573+00:00
-- url     : https://prove2.me/theorems/6ec3ca0f-239a-458f-947c-d66fc04173cc
-- title:
--   Groundwork: sum tuples map
-- statement:
--   A sum over tuples, carried along bijections φ i of T' i with T i.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L176-L205
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L176-L205

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Definitions.Def_StepMachines_Math_CodeMore
set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}

theorem Groundwork.sum_tuples_map {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid M] (P : ι → Prop) [DecidablePred P]
    {T : ι → Finset X} {T' : ι → Finset Y} (d : X) (d' : Y) (φ : ι → Y → X) (h : ∀ i, P i → Set.BijOn (φ i) (T' i) (T i))
    (F : (ι → X) → M) :
    ∑ t ∈ tuples P T d, F t = ∑ t' ∈ tuples P T' d', F fun i => if P i then φ i (t' i) else d := by sorry
