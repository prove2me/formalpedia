-- Prove2me | Theorems.Thm_GeneralPieces_Half_abs_valK_lt
-- name    : GeneralPieces.Half.abs_valK_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:41.618194+00:00
-- url     : https://prove2.me/theorems/e11284bf-6194-4a41-b606-dd8743defe50
-- title:
--   Half: abs val K lt
-- statement:
--   The values that the two programs of a factorization return, at a label that stands for a pair
--   (j, τ) with a listed partition τ, are below 2^{big h}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Size.lean#L68-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Size.lean#L68-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_ThmHalfPieces
import Definitions.Def_GeneralPieces_Half_Order
import Definitions.Def_GeneralPieces_Half_Size
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset GeneralPieces.Ring GeneralPieces.Sizes ClauseBound.Inst.Half

theorem GeneralPieces.Half.abs_valK_lt {h : ℕ} (hh : 1 ≤ h) (tr top : Bool) (s : ℤ) {α β : List ℕ} (hα : ClauseBound.Boson.Pos α ∧ α.sum = h) (hβ : ClauseBound.Boson.Pos β ∧ β.sum = h)
    {p : ℕ × List ℕ} (hp : ClauseBound.Boson.Pos p.2) (hp' : p.2.sum ≤ 4 * h) : |valK tr top h s α β p| < 2 ^ ClauseBound.Boson.big h := by sorry
