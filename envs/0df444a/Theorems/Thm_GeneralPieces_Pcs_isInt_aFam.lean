-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_isInt_aFam
-- name    : GeneralPieces.Pcs.isInt_aFam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:59.761338+00:00
-- url     : https://prove2.me/theorems/2a74b7fa-3c3e-47dc-88da-0c04fe069bbf
-- title:
--   Pcs: is Int a Fam
-- statement:
--   The Pcs construction uses the is Int a Fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L171-L180
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L171-L180

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

theorem GeneralPieces.Pcs.isInt_aFam (μ : Ptn) : IsInt (aFam μ) := by sorry
