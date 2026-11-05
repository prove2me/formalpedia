-- Prove2me | Theorems.Thm_GeneralPieces_ApcL_eq_piece
-- name    : GeneralPieces.ApcL_eq_piece
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:40.612237+00:00
-- url     : https://prove2.me/theorems/5e55c1f0-771c-4aac-9a7c-2a1618ed0709
-- title:
--   General Pieces: Apc L eq piece
-- statement:
--   The integer function that the programs factorize is the piece A_s of the appendix, for μ(x) the
--   partition listed in ℓ(x). By display (55).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L219-L227
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L219-L227

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

theorem GeneralPieces.ApcL_eq_piece (hPF : PieceFacts) (hℓ : ∀ x, ClauseBound.Boson.Pos (ℓ x) ∧ (ℓ x).sum = h) (hh : 1 ≤ h) (s : ℤ) (x y u v : Pieces.Bits lam) :
    ((ClauseBound.Boson.ApcL ℓ h s x y u v : ℤ) : ℚ) = piece h (fun x => ptn (ℓ x)) s x y u v := by sorry
