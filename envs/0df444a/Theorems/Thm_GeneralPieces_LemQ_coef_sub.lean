-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_coef_sub
-- name    : GeneralPieces.LemQ.coef_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:20:14.906312+00:00
-- url     : https://prove2.me/theorems/eba78782-a4ce-487a-9033-28ce5158896b
-- title:
--   Lem Q: coef sub
-- statement:
--   The Lem Q construction uses the coef sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L57-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L57-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.LemQ.coef_sub (π : Ptn) (f g : V) : coef π (f - g) = coef π f - coef π g := by sorry
