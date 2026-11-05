-- Prove2me | Theorems.Thm_GeneralPieces_Half_abs_ApcL_lt
-- name    : GeneralPieces.Half.abs_ApcL_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:33.322343+00:00
-- url     : https://prove2.me/theorems/b4d26972-d984-4a74-ae27-93c2309727e9
-- title:
--   Half: abs Apc L lt
-- statement:
--   «And A_s is a sum of at most Δ products of two factors»: the size of the integer functions that
--   the programs factorize.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Size.lean#L80-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Size.lean#L80-L85

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

theorem GeneralPieces.Half.abs_ApcL_lt (hPF : PieceFacts) {lam h : ℕ} (hp : 2 ^ lam ≤ Partitions.p h) (hℓ : ∀ x : Pieces.Bits lam, ClauseBound.Boson.Pos (ell h x) ∧ (ell h x).sum = h) (hh : 1 ≤ h)
    {s : ℤ} (hs : |s| ≤ 2 * (h : ℤ)) (x y u v : Pieces.Bits lam) : |ClauseBound.Boson.ApcL (ell h) h s x y u v| < 2 ^ ClauseBound.Boson.big h := by sorry
