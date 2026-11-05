-- Prove2me | Theorems.Thm_GeneralPieces_Half_topK_eq
-- name    : GeneralPieces.Half.topK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:23:30.726882+00:00
-- url     : https://prove2.me/theorems/4fea0aab-9540-45e8-9a3d-4ad73f323b3b
-- title:
--   Half: top K eq
-- statement:
--   The entry (π, σ) of the matrix that carries a^μ is (−1)^i times the coefficient of t^π in
--   (a^μ)^⟨i⟩[r]·t^σ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L195-L205
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L195-L205

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
open GeneralPieces.Half

theorem GeneralPieces.Half.topK_eq {L : List ℕ} {h : ℕ} (hL : ClauseBound.Boson.Pos L) (hs : L.sum = h) (i : ℕ) (r : ℤ) (π σ : Ptn) :
    ((ClauseBound.Boson.topK L h i r (toN π) (toN σ) : ℤ) : ℚ) = (-1) ^ i * coef π (op (angle h i (AppHalfPieces.aFam (ptn L))) r (tpow σ)) := by sorry
