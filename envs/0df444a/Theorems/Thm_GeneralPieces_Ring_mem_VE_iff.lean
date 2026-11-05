-- Prove2me | Theorems.Thm_GeneralPieces_Ring_mem_VE_iff
-- name    : GeneralPieces.Ring.mem_VE_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:29:45.524899+00:00
-- url     : https://prove2.me/theorems/f9187125-daed-4c8e-9367-26a69d7c8db9
-- title:
--   Ring: mem VE iff
-- statement:
--   f has weight E if and only if every monomial of f has weight E.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L102-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Basic.lean#L102-L124

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

theorem GeneralPieces.Ring.mem_VE_iff (E : ℤ) (f : V) : f ∈ VE E ↔ ∀ μ, coef μ f ≠ 0 → (wt μ : ℤ) = E := by sorry
