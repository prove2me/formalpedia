-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_Le_smul
-- name    : GeneralPieces.Pcs.Le.smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:31:33.032166+00:00
-- url     : https://prove2.me/theorems/d5b03a5d-4027-4efa-8c8a-2a7252c8afd6
-- title:
--   Le: smul
-- statement:
--   The Le construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L54-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L54-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_LemmaQ
import Definitions.Def_GeneralPieces_Ring_Pieces
import Theorems.Thm_GeneralPieces_LemQ_Tri_smul

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Pcs
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring GeneralPieces.LemQ

theorem GeneralPieces.Pcs.Le.smul {h : ℕ} {a : V} (ha : Le h a) (q : ℚ) : Le h (q • a) := by sorry
