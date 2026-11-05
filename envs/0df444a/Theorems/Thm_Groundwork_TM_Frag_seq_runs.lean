-- Prove2me | Theorems.Thm_Groundwork_TM_Frag_seq_runs
-- name    : Groundwork.TM.Frag.seq_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:22.354091+00:00
-- url     : https://prove2.me/theorems/f365c680-d08f-4480-86a1-525ca9313a2e
-- title:
--   Frag: seq runs
-- statement:
--   A run of P followed by a run of Q is a run of `P.seq Q`; the numbers of steps add up.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L49-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L49-L52

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

theorem Groundwork.TM.Frag.seq_runs {P Q : Frag Γ σ} {v : σ} {S S' S'' : ∀ k, List (Γ k)} {n n' : ℕ} (hP : P.Runs v S n S')
    (hQ : Q.Runs v S' n' S'') : (P.seq Q).Runs v S (n + n') S'' := by sorry
