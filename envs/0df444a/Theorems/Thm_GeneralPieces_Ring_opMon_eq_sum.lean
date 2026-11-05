-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opMon_eq_sum
-- name    : GeneralPieces.Ring.opMon_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:26.444392+00:00
-- url     : https://prove2.me/theorems/e0256f31-f89c-4a3f-a2bb-95201f897451
-- title:
--   Ring: op Mon eq sum
-- statement:
--   Display (47) on a monomial of weight E as a finite sum: over the lists of nonzero integers
--   between −M and M with sum −r, for any M ≥ E + |r|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L268-L278
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L268-L278

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

theorem GeneralPieces.Ring.opMon_eq_sum (μ : List ℕ+) (r : ℤ) (σ : Ptn) (M : ℕ) (hM : (wt σ : ℤ) + |r| ≤ M) :
    opMon μ r (tpow σ) = ∑ ks ∈ ClauseBound.Boson.tup M μ.length with ks.sum = -r, term μ ks (tpow σ) := by sorry
