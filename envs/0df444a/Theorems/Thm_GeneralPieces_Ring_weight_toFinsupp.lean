-- Prove2me | Theorems.Thm_GeneralPieces_Ring_weight_toFinsupp
-- name    : GeneralPieces.Ring.weight_toFinsupp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:28:39.530908+00:00
-- url     : https://prove2.me/theorems/49de555e-d8bb-4e67-98e0-a25020bca5cd
-- title:
--   Ring: weight to Finsupp
-- statement:
--   The weight of the monomial t^μ is |μ|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L78-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L78-L83

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Bridge
import Definitions.Def_ClauseBound_Part_Rec
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Definitions.Def_GeneralPieces_Ring_Basic
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.weight_toFinsupp (μ : Ptn) : Finsupp.weight wgt (Multiset.toFinsupp μ) = wt μ := by sorry
