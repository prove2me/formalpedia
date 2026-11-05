-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_tpow_mul
-- name    : GeneralPieces.Pcs.tpow_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:18.000848+00:00
-- url     : https://prove2.me/theorems/ca5bba37-3b4f-4206-a9e6-a024f5377942
-- title:
--   Pcs: tpow mul
-- statement:
--   The Pcs construction uses the tpow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L72-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L72-L74

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

theorem GeneralPieces.Pcs.tpow_mul (μ ν : Ptn) : tpow μ * tpow ν = tpow (μ + ν) := by sorry
