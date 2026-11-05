-- Prove2me | Theorems.Thm_Groundwork_Sparsify_leaves_sim
-- name    : Groundwork.Sparsify.leaves_sim
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:12.412195+00:00
-- url     : https://prove2.me/theorems/fa712545-da11-47e8-bd98-b558e2ef4d6f
-- title:
--   Sparsify: leaves sim
-- statement:
--   If f carries step' to step on the states with I, it carries leaves to leaves.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyList.lean#L33-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SparsifyList.lean#L33-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_SparsifyStep
import Definitions.Def_StepMachines_Math_SparsifyCount
import Definitions.Def_ThreeSatStatement
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_StepMachines_Math_SparsifyList
set_option autoImplicit false
section
open Groundwork Groundwork.Sparsify
open Finset
variable {σ σ' : Type*} {step' : σ' → Option (σ' × σ')} {step : σ → Option (σ × σ)} {f : σ' → σ} {I : σ' → Prop}

theorem Groundwork.Sparsify.leaves_sim (hsim : ∀ s, I s → (step' s).map (Prod.map f f) = step (f s))
    (hinv : ∀ s l h, I s → step' s = some (l, h) → I l ∧ I h) (k : ℕ) (s : σ') (hs : I s) :
    (leaves step' k s).map f = leaves step k (f s) ∧ ∀ x ∈ leaves step' k s, I x := by sorry
