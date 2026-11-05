-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_tri_ab
-- name    : GeneralPieces.LemQ.tri_ab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:21:40.577981+00:00
-- url     : https://prove2.me/theorems/82098e81-6257-4b67-88f5-fdc756076341
-- title:
--   Lem Q: tri ab
-- statement:
--   a^⟨i⟩[r] b[r'] f is linear in a, b and f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L195-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L195-L201

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

theorem GeneralPieces.LemQ.tri_ab (hOp : OpFacts) (h i : ℕ) (r r' : ℤ) : Tri fun a b f => op (angle h i a) r (op b r' f) := by sorry
