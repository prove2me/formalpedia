-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_isInt_mul
-- name    : GeneralPieces.Pcs.isInt_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:45.802908+00:00
-- url     : https://prove2.me/theorems/899abc32-39eb-429b-b4f9-fc834ac49672
-- title:
--   Pcs: is Int mul
-- statement:
--   The Pcs construction uses the is Int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L148-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L148-L155

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

theorem GeneralPieces.Pcs.isInt_mul {f g : V} (hf : IsInt f) (hg : IsInt g) : IsInt (f * g) := by sorry
