-- Prove2me | Theorems.Thm_GeneralPieces_Half_aFam_eq
-- name    : GeneralPieces.Half.aFam_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:27.813638+00:00
-- url     : https://prove2.me/theorems/144e24bf-8a35-40cd-bfe2-4ed61c7ee682
-- title:
--   Half: a Fam eq
-- statement:
--   a^μ, multiplied out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L139-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L139-L144

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half

theorem GeneralPieces.Half.aFam_eq {L : List ℕ} (hL : ClauseBound.Boson.Pos L) : AppHalfPieces.aFam (ptn L) = polyOf (ClauseBound.Boson.aFam L) := by sorry
