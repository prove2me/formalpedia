-- Prove2me | Theorems.Thm_GeneralPieces_Dual_mem_tuples
-- name    : GeneralPieces.Dual.mem_tuples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:56.542207+00:00
-- url     : https://prove2.me/theorems/2810259c-0d8e-4697-a129-27f545629fda
-- title:
--   Dual: mem tuples
-- statement:
--   Membership.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L84-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L84-L94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.mem_tuples {α : Type} [DecidableEq α] (L : List (Finset α)) (x : List α) : x ∈ tuples L ↔ List.Forall₂ (fun a s => a ∈ s) x L := by sorry
