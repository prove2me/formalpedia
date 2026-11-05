-- Prove2me | Theorems.Thm_Groundwork_TM_Frag_ofStmt_runs
-- name    : Groundwork.TM.Frag.ofStmt_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:49.23417+00:00
-- url     : https://prove2.me/theorems/21a7fbfe-e8a2-42af-b5ea-80dce0e34a37
-- title:
--   Frag: of Stmt runs
-- statement:
--   If the statement halts with the local state unchanged, the fragment runs in one step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L67-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L67-L69

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

theorem Groundwork.TM.Frag.ofStmt_runs {q : TM2.Stmt Γ Empty σ} {v : σ} {S S' : ∀ k, List (Γ k)}
    (h : TM2.stepAux q v S = ⟨none, v, S'⟩) : (Frag.ofStmt q).Runs v S 1 S' := by sorry
