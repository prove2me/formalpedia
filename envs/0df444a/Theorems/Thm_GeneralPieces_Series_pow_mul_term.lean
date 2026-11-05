-- Prove2me | Theorems.Thm_GeneralPieces_Series_pow_mul_term
-- name    : GeneralPieces.Series.pow_mul_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:17:01.732334+00:00
-- url     : https://prove2.me/theorems/f3bae9b5-9fce-4e4a-9efc-a8b133027d1a
-- title:
--   Series: pow mul term
-- statement:
--   One term: if d·e = 1 and N ≤ H then d^H·(Γ·(e^N·n)) = Γ·(d^{H−N}·n).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L29-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Series/OneLaurent.lean#L29-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Series_Expansion
import Definitions.Def_GeneralPieces_Series_OneLaurent
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Series
open ClauseBound.Boson
variable {a b : List ℕ} {G : ℚ} {π σ : Multiset ℕ}

theorem GeneralPieces.Series.pow_mul_term {A : Type} [CommRing A] [Algebra ℚ A] {d e : A} (h : d * e = 1) {N H : ℕ} (hN : N ≤ H) (r : ℚ) (n : A) :
    d ^ H * (r • (e ^ N * n)) = r • (d ^ (H - N) * n) := by sorry
