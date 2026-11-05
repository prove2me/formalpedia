-- Prove2me | Theorems.Thm_Groundwork_block_polyT
-- name    : Groundwork.block_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:28:18.800139+00:00
-- url     : https://prove2.me/theorems/aa0a4dc6-3b6e-431f-b8eb-8c68dc12f327
-- title:
--   Groundwork: block poly T
-- statement:
--   The Groundwork construction uses the block poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Words.lean#L21-L22
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Words.lean#L21-L22

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

theorem Groundwork.block_polyT {ℓ j : α → ℕ} {w : α → List Bool} (h1 : PolyT ℓ) (h2 : PolyT j) (h3 : PolyT w) :
    PolyT fun x => block (ℓ x) (j x) (w x) := by sorry
