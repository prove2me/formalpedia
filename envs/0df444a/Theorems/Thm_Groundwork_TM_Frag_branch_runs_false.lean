-- Prove2me | Theorems.Thm_Groundwork_TM_Frag_branch_runs_false
-- name    : Groundwork.TM.Frag.branch_runs_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:24.377269+00:00
-- url     : https://prove2.me/theorems/bb16bf60-4baf-4a7f-8daa-bbcb7b48d016
-- title:
--   Frag: branch runs false
-- statement:
--   If the head ends in `goto false`, the branch takes one step and then runs as Q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L88-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L88-L92

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

theorem Groundwork.TM.Frag.branch_runs_false {q : TM2.Stmt Γ Bool σ} {P Q : Frag Γ σ} {v : σ} {S S₁ S' : ∀ k, List (Γ k)} {n : ℕ}
    (h : TM2.stepAux q v S = ⟨some false, v, S₁⟩) (hQ : Q.Runs v S₁ n S') : (Frag.branch q P Q).Runs v S (n + 1) S' := by sorry
