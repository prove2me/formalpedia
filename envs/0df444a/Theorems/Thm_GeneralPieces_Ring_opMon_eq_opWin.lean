-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opMon_eq_opWin
-- name    : GeneralPieces.Ring.opMon_eq_opWin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:26:37.036434+00:00
-- url     : https://prove2.me/theorems/c616dcfe-a2de-424c-9a6c-2c3ea029f6aa
-- title:
--   Ring: op Mon eq op Win
-- statement:
--   a[r]·f is the finite sum, for all large M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L110-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L110-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.opMon_eq_opWin {f : V} {E : ℤ} (hf : Bd f E) (μ : List ℕ+) {r : ℤ} {M : ℕ} (h1 : E ≤ M) (h2 : E + r ≤ M) : opMon μ r f = opWin μ M r f := by sorry
