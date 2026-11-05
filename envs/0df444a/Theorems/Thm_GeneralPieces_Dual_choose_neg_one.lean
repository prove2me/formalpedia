-- Prove2me | Theorems.Thm_GeneralPieces_Dual_choose_neg_one
-- name    : GeneralPieces.Dual.choose_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:43.9272+00:00
-- url     : https://prove2.me/theorems/0fd56c06-9a92-48f2-8f73-f8dcd7551ed5
-- title:
--   Dual: choose neg one
-- statement:
--   C(−1, m) = (−1)^m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L47-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L47-L53

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

theorem GeneralPieces.Dual.choose_neg_one (m : ℕ) : Ring.choose (-1 : ℤ) m = (-1) ^ m := by sorry
