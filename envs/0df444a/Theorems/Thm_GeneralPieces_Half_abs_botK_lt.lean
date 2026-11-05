-- Prove2me | Theorems.Thm_GeneralPieces_Half_abs_botK_lt
-- name    : GeneralPieces.Half.abs_botK_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:49.588962+00:00
-- url     : https://prove2.me/theorems/00cfda85-a2c1-4392-b764-b6c9e1e5e472
-- title:
--   Half: abs bot K lt
-- statement:
--   The entries of the matrix that carries b^ν, at listed partitions, are below 2^{big h}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Size.lean#L57-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Size.lean#L57-L64

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

theorem GeneralPieces.Half.abs_botK_lt {h : ℕ} (hh : 1 ≤ h) {L : List ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (r : ℤ) {π σ : List ℕ} (hπ : ClauseBound.Boson.Pos π)
    (hπ' : π.sum ≤ 4 * h) (hσ : ClauseBound.Boson.Pos σ) (hσ' : σ.sum ≤ 4 * h) : |ClauseBound.Boson.botK L h r (π : Multiset ℕ) (σ : Multiset ℕ)| < 2 ^ ClauseBound.Boson.big h := by sorry
