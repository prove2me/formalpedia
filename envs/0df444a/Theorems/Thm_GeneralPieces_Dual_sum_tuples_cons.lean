-- Prove2me | Theorems.Thm_GeneralPieces_Dual_sum_tuples_cons
-- name    : GeneralPieces.Dual.sum_tuples_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:25:08.2773+00:00
-- url     : https://prove2.me/theorems/8eaefa3f-7540-446f-8a97-38222a28e4ea
-- title:
--   Dual: sum tuples cons
-- statement:
--   A sum over such lists, sorted by the first entry.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L76-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L76-L81

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

theorem GeneralPieces.Dual.sum_tuples_cons {α M : Type} [DecidableEq α] [AddCommMonoid M] (s : Finset α) (r : List (Finset α)) (F : List α → M) :
    ∑ x ∈ tuples (s :: r), F x = ∑ a ∈ s, ∑ x ∈ tuples r, F (a :: x) := by sorry
