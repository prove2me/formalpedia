-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_coef_add
-- name    : GeneralPieces.LemQ.coef_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:20:16.151189+00:00
-- url     : https://prove2.me/theorems/9ed8725e-b9a0-4c2a-8d4c-93f770defecf
-- title:
--   Lem Q: coef add
-- statement:
--   The Lem Q construction uses the coef add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L55-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L55-L55

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

theorem GeneralPieces.LemQ.coef_add (π : Ptn) (f g : V) : coef π (f + g) = coef π f + coef π g := by sorry
