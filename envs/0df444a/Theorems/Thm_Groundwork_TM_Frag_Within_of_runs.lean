-- Prove2me | Theorems.Thm_Groundwork_TM_Frag_Within_of_runs
-- name    : Groundwork.TM.Frag.Within.of_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:28:19.39148+00:00
-- url     : https://prove2.me/theorems/a89b5d3f-265a-4f09-8dd9-1bd5965f43bc
-- title:
--   Within: of runs
-- statement:
--   The Within construction uses the of runs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L137-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L137-L138

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Run
import Definitions.Def_ToTuring_TM_Frag
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
attribute [instance] Frag.fin
variable {τ : Type}

theorem Groundwork.TM.Frag.Within.of_runs {P : Frag Γ (Option τ)} {S S' : ∀ k, List (Γ k)} {n : ℕ} (h : P.Runs none S n S') :
    P.Within S n S' := by sorry
