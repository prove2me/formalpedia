-- Prove2me | Theorems.Thm_Groundwork_PolyT_pred
-- name    : Groundwork.PolyT.pred
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:35:08.452366+00:00
-- url     : https://prove2.me/theorems/c8187166-e625-4ccf-a1d3-e50bfd97eec6
-- title:
--   Poly T: pred
-- statement:
--   The Poly T construction uses the pred property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1.lean#L287-L288
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1.lean#L287-L288

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_ToTuring_Lib_Nat1
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.pred {f : α → ℕ} (hf : PolyT f) :
    PolyT (fun x => f x - 1) := by sorry
