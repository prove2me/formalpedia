-- Prove2me | Theorems.Thm_GeneralPieces_Ring_X_mul_tpow
-- name    : GeneralPieces.Ring.X_mul_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:34:37.922203+00:00
-- url     : https://prove2.me/theorems/e40b4703-4774-40be-ad6b-490a7cc71cd3
-- title:
--   Ring: X mul tpow
-- statement:
--   The Ring construction uses the X mul tpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L126-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L126-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.X_mul_tpow (n : ℕ+) (μ : Ptn) : X n * tpow μ = tpow (n ::ₘ μ) := by sorry
