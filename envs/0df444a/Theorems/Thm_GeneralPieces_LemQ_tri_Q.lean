-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_tri_Q
-- name    : GeneralPieces.LemQ.tri_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:21:42.236233+00:00
-- url     : https://prove2.me/theorems/7095e403-2d1e-420c-88d3-e8cb180463af
-- title:
--   Lem Q: tri Q
-- statement:
--   Q_s(a, b) f is linear in a, b and f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L213-L213
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L213-L213

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

theorem GeneralPieces.LemQ.tri_Q (hOp : OpFacts) (h : ℕ) (s : ℤ) : Tri (Q h s) := by sorry
