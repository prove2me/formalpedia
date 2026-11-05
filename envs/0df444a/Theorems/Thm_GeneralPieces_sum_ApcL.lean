-- Prove2me | Theorems.Thm_GeneralPieces_sum_ApcL
-- name    : GeneralPieces.sum_ApcL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:42.328638+00:00
-- url     : https://prove2.me/theorems/4489bd4b-bfb6-4a16-883d-4f617b19edb7
-- title:
--   General Pieces: sum Apc L
-- statement:
--   Σ_s A_s = h!·[x = v][y = u], from the statement about the ring.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L230-L244
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L230-L244

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open Half
variable {lam h : ℕ} {ℓ : Pieces.Bits lam → List ℕ}

theorem GeneralPieces.sum_ApcL (hPF : PieceFacts) (hℓ : ∀ x, ClauseBound.Boson.Pos (ℓ x) ∧ (ℓ x).sum = h) (hinj : ∀ x v, (ℓ x : Multiset ℕ) = ℓ v → x = v) (hh : 1 ≤ h)
    (x y u v : Pieces.Bits lam) :
    ∑ s ∈ Icc (-(2 * h : ℤ)) (2 * h), ClauseBound.Boson.ApcL ℓ h s x y u v = h.factorial * Pieces.cross x y u v := by sorry
