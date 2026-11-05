-- Prove2me | Theorems.Thm_GeneralPieces_Ring_finite_terms
-- name    : GeneralPieces.Ring.finite_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:21.562193+00:00
-- url     : https://prove2.me/theorems/b75828b5-d127-4d28-82a9-d04b272f27cf
-- title:
--   Ring: finite terms
-- statement:
--   "So only finitely many terms are nonzero."
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L127-L133
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L127-L133

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

theorem GeneralPieces.Ring.finite_terms (μ : List ℕ+) (r : ℤ) (f : V) : {ks ∈ Choices μ r | term μ ks f ≠ 0}.Finite := by sorry
