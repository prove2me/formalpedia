-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_isInt_tpow
-- name    : GeneralPieces.Pcs.isInt_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:20.233298+00:00
-- url     : https://prove2.me/theorems/130e7f42-0111-44c3-871f-b99dc0ddae7f
-- title:
--   Pcs: is Int tpow
-- statement:
--   The Pcs construction uses the is Int tpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L157-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L157-L163

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

theorem GeneralPieces.Pcs.isInt_tpow (μ : Ptn) : IsInt (tpow μ) := by sorry
