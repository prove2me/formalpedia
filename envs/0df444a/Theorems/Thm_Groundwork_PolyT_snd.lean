-- Prove2me | Theorems.Thm_Groundwork_PolyT_snd
-- name    : Groundwork.PolyT.snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:15.659401+00:00
-- url     : https://prove2.me/theorems/f6286b53-1381-4702-866b-7d66d8ff2de1
-- title:
--   Poly T: snd
-- statement:
--   The Poly T construction uses the snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L117-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L117-L118

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Closure_Basic
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
open TM Enc
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.snd {f : α → β × γ} (hf : PolyT f) : PolyT (fun x => (f x).2) := by sorry
