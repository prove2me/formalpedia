-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_isInt_part
-- name    : GeneralPieces.Pcs.isInt_part
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:24:00.844859+00:00
-- url     : https://prove2.me/theorems/d4f2b947-f8a9-4a20-9214-bbc0390f0e8e
-- title:
--   Pcs: is Int part
-- statement:
--   The Pcs construction uses the is Int part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L182-L188
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L182-L188

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

theorem GeneralPieces.Pcs.isInt_part {a : V} (ha : IsInt a) (h' : ℕ) : IsInt (part h' a) := by sorry
