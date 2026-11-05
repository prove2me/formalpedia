-- Prove2me | Theorems.Thm_Groundwork_PolyT_fst
-- name    : Groundwork.PolyT.fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:46:13.417584+00:00
-- url     : https://prove2.me/theorems/0931b2a3-e9cf-4a20-89fe-b66437bff231
-- title:
--   Poly T: fst
-- statement:
--   The Poly T construction uses the fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L115-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Closure/Basic.lean#L115-L116

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

theorem Groundwork.PolyT.fst {f : α → β × γ} (hf : PolyT f) : PolyT (fun x => (f x).1) := by sorry
