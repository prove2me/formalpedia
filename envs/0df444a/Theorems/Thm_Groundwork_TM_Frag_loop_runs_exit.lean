-- Prove2me | Theorems.Thm_Groundwork_TM_Frag_loop_runs_exit
-- name    : Groundwork.TM.Frag.loop_runs_exit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:21.280198+00:00
-- url     : https://prove2.me/theorems/aeb08544-a6e3-450a-8813-3e9740a86dd0
-- title:
--   Frag: loop runs exit
-- statement:
--   If the head halts, the loop ends after one step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L104-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L104-L106

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

theorem Groundwork.TM.Frag.loop_runs_exit {q : TM2.Stmt Γ Unit σ} {B : Frag Γ σ} {v : σ} {S S' : ∀ k, List (Γ k)}
    (h : TM2.stepAux q v S = ⟨none, v, S'⟩) : (Frag.loop q B).Runs v S 1 S' := by sorry
