-- Prove2me | Theorems.Thm_GeneralPieces_Trim_valF_eq_sum
-- name    : GeneralPieces.Trim.valF_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:59.630021+00:00
-- url     : https://prove2.me/theorems/bbcec0c3-37aa-4ea0-940b-b8b1d083b199
-- title:
--   Trim: val F eq sum
-- statement:
--   If the pad is long enough for the loop, `valF` is the sum of top·bot over all words of `cap`
--   bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Prog.lean#L41-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Prog.lean#L41-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_DefGenPieces_Progs
import Definitions.Def_GeneralPieces_Trim_Prog
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen
open GeneralPieces.Trim

theorem GeneralPieces.Trim.valF_eq_sum (P : PiecesF) {pad : U} {tr : Bool} {h lam i : ℕ} (hp : 2 ^ P.cap tr h lam i ≤ pad.length) (a b a' b' : Pieces.Bits lam) :
    valF P ((pad, tr), (rep h, i), (bitsOf a, bitsOf b, bitsOf a', bitsOf b')) =
      ∑ θ ∈ words (P.cap tr h lam i), P.top ((pad, tr), (h, i), (bitsOf a, bitsOf b, θ)) * P.bot ((pad, tr), (h, i), (bitsOf a', bitsOf b', θ)) := by sorry
