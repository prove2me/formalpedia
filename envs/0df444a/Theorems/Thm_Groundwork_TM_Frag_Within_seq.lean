-- Prove2me | Theorems.Thm_Groundwork_TM_Frag_Within_seq
-- name    : Groundwork.TM.Frag.Within.seq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:21:08.210498+00:00
-- url     : https://prove2.me/theorems/547f4f8a-eb04-4dfb-9342-591fdfd2a9fa
-- title:
--   Within: seq
-- statement:
--   The Within construction uses the seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L131-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L131-L135

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

theorem Groundwork.TM.Frag.Within.seq {P Q : Frag Γ (Option τ)} {S S' S'' : ∀ k, List (Γ k)} {t t' : ℕ} (h : P.Within S t S')
    (h' : Q.Within S' t' S'') : (P.seq Q).Within S (t + t') S'' := by sorry
