-- Prove2me | Theorems.Thm_GeneralPieces_Level_enum_spec2
-- name    : GeneralPieces.Level.enum_spec2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:36.773174+00:00
-- url     : https://prove2.me/theorems/7967fa9e-ffc5-4356-8df0-fb674a14b2a9
-- title:
--   Level: enum spec2
-- statement:
--   One term of the sum over ι (a pattern, numbered y) whose column network is evaluated by
--   enumeration: the result is the value of the network, and it is small.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Level.lean#L100-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Level.lean#L100-L131

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Level
import Definitions.Def_GeneralPieces_Rec_Level
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Level
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.Level Finset

theorem GeneralPieces.Level.enum_spec2 (hE : StEnum) (P : PiecesF) (pad : U) (s : Step) (lam B : ℕ) (I : PInst) (y : ℕ) (hL : LevelOK2 P s lam) (hlam : I.1.length = lam)
    (hb : BudG P pad.length s lam) (hy : y < nPat P s lam) (hc : (s.thin && colSide P s lam y) = true)
    (N : Network (Fin s.d) (List Bool) (List Bool)) (hN : (gridF P).toP.Presents (gctx pad s true I y) N 0 0)
    (hS : N.Sized (P.m * (s.d * s.p ^ 2 * lam)) (s.p * B + s.p ^ 2 * P.bits s.h lam))
    (hU : N.U = totalG P s.p s.d true s.h lam y) :
    enumF pad s.d (gridF P) (gctx pad s true I y) = N.value ∧ |N.value| ≤ 2 ^ (Nof s lam + s.d ^ 2 * (s.p * B + s.p ^ 2 * P.bits s.h lam)) := by sorry
