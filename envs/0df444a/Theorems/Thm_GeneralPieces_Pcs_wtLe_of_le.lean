-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_wtLe_of_le
-- name    : GeneralPieces.Pcs.wtLe_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:14.895452+00:00
-- url     : https://prove2.me/theorems/924e5140-4609-418f-85b0-691796b99513
-- title:
--   Pcs: wt Le of le
-- statement:
--   The Pcs construction uses the wt Le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L38-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L38-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem GeneralPieces.Pcs.wtLe_of_le {h : ℕ} {a : V} (ha : Le h a) : WtLe h a := by sorry
