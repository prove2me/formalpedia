-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_angle_smul
-- name    : GeneralPieces.LemQ.angle_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:11.687531+00:00
-- url     : https://prove2.me/theorems/c81edc2d-2631-44fb-875a-2864b528c155
-- title:
--   Lem Q: angle smul
-- statement:
--   The Lem Q construction uses the angle smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L189-L192
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L189-L192

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

theorem GeneralPieces.LemQ.angle_smul (h i : ℕ) (q : ℚ) (a : V) : angle h i (q • a) = q • angle h i a := by sorry
