-- Prove2me | Theorems.Thm_Groundwork_TM_Frag_loop_runs_iter
-- name    : Groundwork.TM.Frag.loop_runs_iter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:30:27.168423+00:00
-- url     : https://prove2.me/theorems/b0a8577c-834b-4a8c-81f4-bfc92a4a0285
-- title:
--   Frag: loop runs iter
-- statement:
--   If the head ends in `goto ()`, the loop takes one step, runs the body, then runs as the loop
--   again.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L110-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L110-L114

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

theorem Groundwork.TM.Frag.loop_runs_iter {q : TM2.Stmt Γ Unit σ} {B : Frag Γ σ} {v : σ} {S S₁ S₂ S' : ∀ k, List (Γ k)} {n m : ℕ}
    (h : TM2.stepAux q v S = ⟨some (), v, S₁⟩) (hB : B.Runs v S₁ n S₂) (hL : (Frag.loop q B).Runs v S₂ m S') :
    (Frag.loop q B).Runs v S (1 + n + m) S' := by sorry
