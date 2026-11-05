-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_tri_pairing
-- name    : GeneralPieces.LemQ.tri_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:22:09.051384+00:00
-- url     : https://prove2.me/theorems/c0cb11c3-89ac-4dbd-9f16-6446c82f8dd7
-- title:
--   Lem Q: tri pairing
-- statement:
--   (a[−h]b)·f is linear in a, b and f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L219-L225
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L219-L225

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

theorem GeneralPieces.LemQ.tri_pairing (hOp : OpFacts) (h : ℕ) : Tri fun a b f => pairing h a b • f := by sorry
