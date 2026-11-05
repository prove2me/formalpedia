-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_part_tpow
-- name    : GeneralPieces.LemQ.part_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:22:13.400473+00:00
-- url     : https://prove2.me/theorems/ff7ebbed-8d47-46c4-bb7b-d6d41c333c55
-- title:
--   Lem Q: part tpow
-- statement:
--   The Lem Q construction uses the part tpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L244-L259
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L244-L259

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

theorem GeneralPieces.LemQ.part_tpow (h' : ℕ) (μ : Ptn) : part h' (tpow μ) = if h' = wt μ then tpow μ else 0 := by sorry
