-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_pairing_mon
-- name    : GeneralPieces.LemQ.pairing_mon
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:22:34.952217+00:00
-- url     : https://prove2.me/theorems/9872ef2d-129b-470b-8ab9-939a095a0242
-- title:
--   Lem Q: pairing mon
-- statement:
--   The number a[−h]b for monomials a and b is the entry in the row of the monomial 1 and the column
--   of b of the matrix of a[−h].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L335-L340
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L335-L340

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.LemQ.pairing_mon (hB : StBridge) (hOp : OpFacts) (h : ℕ) (μ ν : Ptn) :
    pairing h (tpow μ) (tpow ν) = (ClauseBound.Boson.op (lst μ) (-(h : ℤ)) 0 (toN ν) : ℚ) := by sorry
