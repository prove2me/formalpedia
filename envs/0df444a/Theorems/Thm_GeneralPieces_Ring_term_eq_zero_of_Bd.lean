-- Prove2me | Theorems.Thm_GeneralPieces_Ring_term_eq_zero_of_Bd
-- name    : GeneralPieces.Ring.term_eq_zero_of_Bd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:07:46.194634+00:00
-- url     : https://prove2.me/theorems/7965a78c-e0e2-45e9-9c5e-b3042983dee4
-- title:
--   Ring: term eq zero of Bd
-- statement:
--   A term of (47) vanishes on f unless all k_i lie between −M and M, if the monomials of f have
--   weight at most E, E ≤ M and E + r ≤ M.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L99-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L99-L104

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

theorem GeneralPieces.Ring.term_eq_zero_of_Bd {f : V} {E : ℤ} (hf : Bd f E) (μ : List ℕ+) {r : ℤ} {M : ℕ} (h1 : E ≤ M) (h2 : E + r ≤ M) (ks : List ℤ) (hs : ks.sum = -r)
    (hb : ∃ k ∈ ks, k < -(M : ℤ) ∨ (M : ℤ) < k) : term μ ks f = 0 := by sorry
