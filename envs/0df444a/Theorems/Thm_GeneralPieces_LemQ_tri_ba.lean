-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_tri_ba
-- name    : GeneralPieces.LemQ.tri_ba
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:21:30.987744+00:00
-- url     : https://prove2.me/theorems/e531af05-8cf3-4600-95d4-47417b447aad
-- title:
--   Lem Q: tri ba
-- statement:
--   b[r'] a^⟨i⟩[r] f is linear in a, b and f.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L204-L210
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L204-L210

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

theorem GeneralPieces.LemQ.tri_ba (hOp : OpFacts) (h i : ℕ) (r r' : ℤ) : Tri fun a b f => op b r' (op (angle h i a) r f) := by sorry
