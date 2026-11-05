-- Prove2me | Theorems.Thm_GeneralPieces_Pcs_le_aFam
-- name    : GeneralPieces.Pcs.le_aFam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:23:37.808684+00:00
-- url     : https://prove2.me/theorems/90740d48-8416-4eb7-8305-ff0686800889
-- title:
--   Pcs: le a Fam
-- statement:
--   "Here a^μ is a combination of monomials of weight at most h."
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L118-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Pieces.lean#L118-L125

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

theorem GeneralPieces.Pcs.le_aFam (μ : Ptn) : Le (wt μ) (aFam μ) := by sorry
