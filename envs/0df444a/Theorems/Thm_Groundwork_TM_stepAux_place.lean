-- Prove2me | Theorems.Thm_Groundwork_TM_stepAux_place
-- name    : Groundwork.TM.stepAux_place
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:55:11.433111+00:00
-- url     : https://prove2.me/theorems/af64d333-ef09-41fe-b889-7a5c7e9700f0
-- title:
--   TM: step Aux place
-- statement:
--   The TM construction uses the step Aux place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean#L68-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Run.lean#L68-L74

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

theorem Groundwork.TM.stepAux_place (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (place ι e q) v S = placeCfg ι e (TM2.stepAux q v S) := by sorry
