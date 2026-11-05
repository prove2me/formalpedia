-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_coe_lst
-- name    : GeneralPieces.LemQ.coe_lst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:16.202167+00:00
-- url     : https://prove2.me/theorems/2863aa18-792a-425a-8831-cee683a984a5
-- title:
--   Lem Q: coe lst
-- statement:
--   The Lem Q construction uses the coe lst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L232-L234
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L232-L234

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

theorem GeneralPieces.LemQ.coe_lst (μ : Ptn) : (lst μ : Multiset ℕ) = toN μ := by sorry
