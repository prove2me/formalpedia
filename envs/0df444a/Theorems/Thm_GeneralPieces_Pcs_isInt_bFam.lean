-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_isInt_bFam
-- name    : GeneralPieces.Pcs.isInt_bFam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:24:20.41948+00:00
-- url     : https://prove2.me/theorems/a82b80f7-46f1-482e-8e4c-3c168229daa0
-- title:
--   Pcs: is Int b Fam
-- statement:
--   b^ν has integer coefficients, because h!/z_ν is an integer.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L197-L205
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L197-L205

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

theorem GeneralPieces.Pcs.isInt_bFam (hZ : ZDvd) (ν : Ptn) : IsInt (bFam ν) := by sorry
