-- Prove2me | Theorems.Thm_Groundwork_TM_run_head
-- name    : Groundwork.TM.run_head
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:32:29.641711+00:00
-- url     : https://prove2.me/theorems/26aa91b2-29ad-4d3b-a9f4-faa2f9abdcb4
-- title:
--   TM: run head
-- statement:
--   One step of a larger machine at a label that holds a placed statement.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L55-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L55-L58

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

theorem Groundwork.TM.run_head {Λ Λ' : Type} {M' : Λ' → TM2.Stmt Γ Λ' σ} (ι : Λ → Λ') (e : Option Λ') {l' : Λ'} {q : TM2.Stmt Γ Λ σ}
    (hM : M' l' = place ι e q) {v : σ} {S : ∀ k, List (Γ k)} {c : TM2.Cfg Γ Λ σ} (h : TM2.stepAux q v S = c) :
    Run (TM2.step M') ⟨some l', v, S⟩ 1 (placeCfg ι e c) := by sorry
