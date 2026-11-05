-- Prove2me | Theorems.Thm_GeneralPieces_Ring_Pz_eq
-- name    : GeneralPieces.Ring.Pz_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:24:37.351007+00:00
-- url     : https://prove2.me/theorems/718f6fa7-bd54-4fd9-8d74-db665d25bb9b
-- title:
--   Ring: Pz eq
-- statement:
--   The index set `ClauseBound.Boson.Pz m`, the multisets of natural numbers without 0 with sum m,
--   is the image of the partitions of m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L138-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L138-L147

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

theorem GeneralPieces.Ring.Pz_eq (m : ℤ) : ClauseBound.Boson.Pz m = (ptnsZ m).image toN := by sorry
