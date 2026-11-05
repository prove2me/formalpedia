-- Prove2me | Theorems.Thm_GeneralPieces_ApcL_row_eq
-- name    : GeneralPieces.ApcL_row_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:59.699251+00:00
-- url     : https://prove2.me/theorems/e6b77ca4-3002-43ee-854f-26dd4ce6fac3
-- title:
--   General Pieces: Apc L row eq
-- statement:
--   Display (54) for the matrices, from the statement about the ring.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L247-L259
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L247-L259

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

theorem GeneralPieces.ApcL_row_eq (hPF : PieceFacts) (hℓ : ∀ x, ClauseBound.Boson.Pos (ℓ x) ∧ (ℓ x).sum = h) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    ClauseBound.Boson.ApcL ℓ h s x y u v = ∑ i ∈ range (2 * h + 1), ∑ τ ∈ ClauseBound.Boson.Pz (s + i),
      ClauseBound.Boson.topK (ℓ x) h i (s - h + i) τ (ℓ y : Multiset ℕ) * ClauseBound.Boson.botK (ℓ v) h (h - s - i) (ℓ u : Multiset ℕ) τ := by sorry
