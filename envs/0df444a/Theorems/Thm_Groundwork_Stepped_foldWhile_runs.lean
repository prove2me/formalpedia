-- Prove2me | Theorems.Thm_Groundwork_Stepped_foldWhile_runs
-- name    : Groundwork.Stepped.foldWhile_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:01.73985+00:00
-- url     : https://prove2.me/theorems/53ff6937-524e-41d6-af98-904d72c234a9
-- title:
--   Stepped: fold While runs
-- statement:
--   The loop: steps = Σ over the orbit of (steps of the body + 1); result = the fold over the orbit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L275-L280
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L275-L280

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}
variable [HasSize τ] [HasSize γ] {start : α → Option τ} {nxt : τ → Option τ} {M : Stepped τ β}
  {g : γ → τ → β → γ} {c₀ : α → γ}

theorem Groundwork.Stepped.foldWhile_runs {a : α} {xs : List τ} (ho : Orbit nxt (start a) xs) (t : τ → ℕ) (v : τ → β)
    (Sx Sc Sm : ℕ) (hM : ∀ x ∈ xs, M.Runs x (t x) Sm (v x)) (hx : ∀ x ∈ xs, size x ≤ Sx)
    (hc : ∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) (c₀ a)) ≤ Sc) :
    (foldWhile start nxt M g c₀).Runs a (xs.map fun x => t x + 1).sum (Sx + (Sc + Sm) + 1)
      (xs.foldl (fun c x => g c x (v x)) (c₀ a)) := by sorry
