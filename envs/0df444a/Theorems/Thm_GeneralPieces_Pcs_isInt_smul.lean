-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_isInt_smul
-- name    : GeneralPieces.Pcs.isInt_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:04.992699+00:00
-- url     : https://prove2.me/theorems/d0393a50-8c06-4b64-b887-2a63725de439
-- title:
--   Pcs: is Int smul
-- statement:
--   The Pcs construction uses the is Int smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L144-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L144-L146

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

theorem GeneralPieces.Pcs.isInt_smul {f : V} (hf : IsInt f) (z : ℤ) : IsInt ((z : ℚ) • f) := by sorry
