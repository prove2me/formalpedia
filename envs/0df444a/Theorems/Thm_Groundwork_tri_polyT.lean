-- Prove2me | Theorems.Thm_Groundwork_tri_polyT
-- name    : Groundwork.tri_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:28:49.43818+00:00
-- url     : https://prove2.me/theorems/c7608078-a070-4da2-99aa-d27e5667c3fb
-- title:
--   Groundwork: tri poly T
-- statement:
--   The Groundwork construction uses the tri poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Words.lean#L24-L25
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Words.lean#L24-L25

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

theorem Groundwork.tri_polyT {a b : α → ℕ} (h1 : PolyT a) (h2 : PolyT b) : PolyT fun x => tri (a x) (b x) := by sorry
