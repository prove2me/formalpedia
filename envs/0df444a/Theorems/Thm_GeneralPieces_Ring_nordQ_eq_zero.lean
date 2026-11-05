-- Prove2me | Theorems.Thm_GeneralPieces_Ring_nordQ_eq_zero
-- name    : GeneralPieces.Ring.nordQ_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:07:34.004307+00:00
-- url     : https://prove2.me/theorems/fd94ad69-e9e8-45ef-82be-244de78ede44
-- title:
--   Ring: nord Q eq zero
-- statement:
--   "A term vanishes if its positive k_i add up to more than E."
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L80-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L80-L95

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

theorem GeneralPieces.Ring.nordQ_eq_zero {f : V} {E : ℤ} (hf : Bd f E) (ks : List ℤ) (h : E < (ks.filter (0 < ·)).sum) : nordQ ks f = 0 := by sorry
