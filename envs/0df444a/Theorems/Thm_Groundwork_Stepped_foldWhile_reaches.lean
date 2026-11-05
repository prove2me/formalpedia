-- Prove2me | Theorems.Thm_Groundwork_Stepped_foldWhile_reaches
-- name    : Groundwork.Stepped.foldWhile_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:33.845815+00:00
-- url     : https://prove2.me/theorems/2e1459b3-430f-4dab-bfb9-bb5faec3e2bd
-- title:
--   Stepped: fold While reaches
-- statement:
--   The Stepped construction uses the fold While reaches property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L254-L272
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L254-L272

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

theorem Groundwork.Stepped.foldWhile_reaches {xs : List τ} {o : Option τ} (ho : Orbit nxt o xs) (t : τ → ℕ) (v : τ → β)
    (Sx Sc Sm : ℕ) (c : γ) (hM : ∀ x ∈ xs, M.Runs x (t x) Sm (v x)) (hx : ∀ x ∈ xs, size x ≤ Sx)
    (hc : ∀ l, l <+: xs → size (l.foldl (fun c x => g c x (v x)) c) ≤ Sc) :
    (foldWhile start nxt M g c₀).Reaches (Sx + (Sc + Sm) + 1) (xs.foldl (fun c x => g c x (v x)) c)
      (foldGo M c o) (xs.map fun x => t x + 1).sum := by sorry
