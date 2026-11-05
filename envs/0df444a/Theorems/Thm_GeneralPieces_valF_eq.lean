-- Prove2me | Theorems.Thm_GeneralPieces_valF_eq
-- name    : GeneralPieces.valF_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:13.980872+00:00
-- url     : https://prove2.me/theorems/ceebfd25-bf8b-4286-beb8-426fcab1d3d5
-- title:
--   General Pieces: val F eq
-- statement:
--   For part (c) of the definition of pieces (one algorithm computes every value of the A_i): when
--   the pad is long enough, `valF` is the value of the piece, from either
--   factorization.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Prog.lean#L56-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Prog.lean#L56-L61

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
open Trim

theorem GeneralPieces.valF_eq {P : PiecesF} {h lam : ℕ} {A : ℕ → Pieces.Four lam} (hA : Realizes P h lam A) {pad : U} (hn : 2 ^ P.need h lam ≤ pad.length) {i : ℕ}
    (hi : i < P.cnt h lam) (hc : ∀ tr, 2 ^ P.cap tr h lam i ≤ pad.length) (x y u v : Pieces.Bits lam) :
    valF P ((pad, false), (rep h, i), (bitsOf x, bitsOf y, bitsOf u, bitsOf v)) = A i x y u v ∧
      valF P ((pad, true), (rep h, i), (bitsOf x, bitsOf u, bitsOf y, bitsOf v)) = A i x y u v := by sorry
