-- Prove2me | Theorems.Thm_GeneralPieces_Ring_filter_sums
-- name    : GeneralPieces.Ring.filter_sums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:29:24.69178+00:00
-- url     : https://prove2.me/theorems/7a1c9e43-fdf4-4903-ba1e-3caca10c64d9
-- title:
--   Ring: filter sums
-- statement:
--   The negative and the positive entries of a list of integers: their sums add up to the sum of the
--   list, and every entry lies between them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L232-L253
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L232-L253

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.filter_sums (ks : List ℤ) : (ks.filter (· < 0)).sum ≤ 0 ∧ 0 ≤ (ks.filter (0 < ·)).sum ∧ ks.sum = (ks.filter (· < 0)).sum + (ks.filter (0 < ·)).sum ∧
    ∀ k ∈ ks, (ks.filter (· < 0)).sum ≤ k ∧ k ≤ (ks.filter (0 < ·)).sum := by sorry
