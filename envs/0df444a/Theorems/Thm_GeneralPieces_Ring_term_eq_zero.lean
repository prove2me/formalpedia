-- Prove2me | Theorems.Thm_GeneralPieces_Ring_term_eq_zero
-- name    : GeneralPieces.Ring.term_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:01:39.349816+00:00
-- url     : https://prove2.me/theorems/4f145cf1-5193-4c40-a995-b09c8e194e13
-- title:
--   Ring: term eq zero
-- statement:
--   On a monomial of weight E, a term of (47) vanishes unless all k_i lie between −(E + |r|) and E + |r|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L256-L264
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L256-L264

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

theorem GeneralPieces.Ring.term_eq_zero (μ : List ℕ+) (r : ℤ) (σ : Ptn) (ks : List ℤ) (hs : ks.sum = -r) (hb : ∃ k ∈ ks, k < -((wt σ : ℤ) + |r|) ∨ (wt σ : ℤ) + |r| < k) :
    term μ ks (tpow σ) = 0 := by sorry
