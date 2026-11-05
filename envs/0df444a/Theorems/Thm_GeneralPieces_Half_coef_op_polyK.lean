-- Prove2me | Theorems.Thm_GeneralPieces_Half_coef_op_polyK
-- name    : GeneralPieces.Half.coef_op_polyK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:56.523481+00:00
-- url     : https://prove2.me/theorems/c6c4514f-5918-4918-96e4-ccc4a00cc91a
-- title:
--   Half: coef op poly K
-- statement:
--   The coefficient of t^π in a[r]·t^σ for a combination a of monomials: the same combination of the
--   entries of the matrices.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L180-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L180-L191

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half

theorem GeneralPieces.Half.coef_op_polyK (k : ℤ × List ℕ → ℚ) {A : ClauseBound.Boson.FA} (hA : ∀ c ∈ A, ClauseBound.Boson.Pos c.2) (r : ℤ) (π σ : Ptn) :
    coef π (op (polyK k A) r (tpow σ)) = (A.map fun c => k c * ((ClauseBound.Boson.op c.2 r (toN π) (toN σ) : ℤ) : ℚ)).sum := by sorry
