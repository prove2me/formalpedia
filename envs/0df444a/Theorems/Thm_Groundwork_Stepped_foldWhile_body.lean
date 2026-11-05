-- Prove2me | Theorems.Thm_Groundwork_Stepped_foldWhile_body
-- name    : Groundwork.Stepped.foldWhile_body
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:57.489276+00:00
-- url     : https://prove2.me/theorems/826475e5-0bf9-4327-8d86-0d05ca06d2be
-- title:
--   Stepped: fold While body
-- statement:
--   The body, run inside the loop.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L234-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L234-L252

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

theorem Groundwork.Stepped.foldWhile_body {x : τ} {c r : γ} {b : β} {s : M.σ} {t T Sm S : ℕ} (h : M.Reaches Sm b s t)
    (hS : size x + (size c + Sm) + 1 ≤ S)
    (hr : (foldWhile start nxt M g c₀).Reaches S r (foldGo M (g c x b) (nxt x)) T) :
    (foldWhile start nxt M g c₀).Reaches S r (.inl (x, c, s)) (t + 1 + T) := by sorry
