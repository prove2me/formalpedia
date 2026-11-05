-- Prove2me | Theorems.Thm_Groundwork_TM_run_place
-- name    : Groundwork.TM.run_place
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:41.693322+00:00
-- url     : https://prove2.me/theorems/e2936b21-5c06-404b-adef-ab748c8f638c
-- title:
--   TM: run place
-- statement:
--   If the larger machine M' holds the placed statements of M, every run of M is a run of M' of the
--   same length.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean#L78-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean#L78-L85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Computability.TuringMachine.Computable
import Definitions.Def_ToTuring_TM_Run
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}
variable {Λ Λ' : Type} (ι : Λ → Λ') (e : Option Λ')

theorem Groundwork.TM.run_place {M : Λ → TM2.Stmt Γ Λ σ} {M' : Λ' → TM2.Stmt Γ Λ' σ} (hM : ∀ l, M' (ι l) = place ι e (M l)) :
    ∀ {n : ℕ} {a b : TM2.Cfg Γ Λ σ}, Run (TM2.step M) a n b → Run (TM2.step M') (placeCfg ι e a) n (placeCfg ι e b)
  := by sorry
