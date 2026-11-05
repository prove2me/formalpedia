-- Prove2me | Theorems.Thm_GeneralPieces_Series_mul2_eq_zero
-- name    : GeneralPieces.Series.mul2_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:38.431572+00:00
-- url     : https://prove2.me/theorems/3afc22c2-8e4c-4f1c-84ad-30832e8195c9
-- title:
--   Series: mul2 eq zero
-- statement:
--   b[r'] vanishes on monomials of weight below −r', and so does every product a[r]∘b[r'].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Expansion.lean#L31-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/Expansion.lean#L31-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Rings
import Definitions.Def_ClauseBound_Boson_Defs
import Definitions.Def_GeneralPieces_Series_Expansion
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson

theorem GeneralPieces.Series.mul2_eq_zero (a b : List ℕ) (r : ℤ) {r' : ℤ} (π : Multiset ℕ) {σ : Multiset ℕ} (h : (σ.sum : ℤ) + r' < 0) : mul2 a r b r' π σ = 0 := by sorry
