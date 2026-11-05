-- Prove2me | Theorems.Thm_GeneralPieces_Ring_eq_sum_tpow
-- name    : GeneralPieces.Ring.eq_sum_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:01:45.788088+00:00
-- url     : https://prove2.me/theorems/a7c6a147-2f50-4472-ac73-928c095b9b38
-- title:
--   Ring: eq sum tpow
-- statement:
--   A polynomial is the sum of its monomials.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L131-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L131-L135

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

theorem GeneralPieces.Ring.eq_sum_tpow (f : V) : f = ∑ d ∈ f.support, coeff d f • tpow (Finsupp.toMultiset d) := by sorry
