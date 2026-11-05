-- Prove2me | Theorems.Thm_Groundwork_query0_polyT
-- name    : Groundwork.query0_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:28:58.24068+00:00
-- url     : https://prove2.me/theorems/6d3acc0e-5ea2-4d0e-99b5-608d35873188
-- title:
--   Groundwork: query0 poly T
-- statement:
--   The Groundwork construction uses the query0 poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Words.lean#L27-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Words.lean#L27-L29

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_StepMachines_Prog_Brute
import Definitions.Def_ToTuring_Poly_Words
set_option autoImplicit false
section
section
open Groundwork
variable {α : Type} [Enc α]

theorem Groundwork.query0_polyT (K : ℕ) {ℓ v : α → ℕ} {d w : α → List Bool} (h1 : PolyT ℓ) (h2 : PolyT d) (h3 : PolyT w)
    (h4 : PolyT v) : PolyT fun x => query0 K (ℓ x) (d x) (w x) (v x) := by sorry
