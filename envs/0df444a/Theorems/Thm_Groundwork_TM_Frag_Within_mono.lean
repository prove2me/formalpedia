-- Prove2me | Theorems.Thm_Groundwork_TM_Frag_Within_mono
-- name    : Groundwork.TM.Frag.Within.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:20:23.032632+00:00
-- url     : https://prove2.me/theorems/b3daf60f-0a67-471b-93c5-e8a035a44f88
-- title:
--   Within: mono
-- statement:
--   The Within construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L126-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Frag.lean#L126-L129

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

theorem Groundwork.TM.Frag.Within.mono {P : Frag Γ (Option τ)} {S S' : ∀ k, List (Γ k)} {t t' : ℕ} (h : P.Within S t S') (ht : t ≤ t') :
    P.Within S t' S' := by sorry
