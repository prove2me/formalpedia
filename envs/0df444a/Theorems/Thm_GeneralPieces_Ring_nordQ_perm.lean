-- Prove2me | Theorems.Thm_GeneralPieces_Ring_nordQ_perm
-- name    : GeneralPieces.Ring.nordQ_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:43.241435+00:00
-- url     : https://prove2.me/theorems/30c48cf7-e1c8-4697-ad4a-da05ae056f52
-- title:
--   Ring: nord Q perm
-- statement:
--   The multiplications commute, and so do the differentiations.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L225-L230
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L225-L230

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

theorem GeneralPieces.Ring.nordQ_perm {ks ks' : List ℤ} (h : ks.Perm ks') (f : V) : nordQ ks f = nordQ ks' f := by sorry
