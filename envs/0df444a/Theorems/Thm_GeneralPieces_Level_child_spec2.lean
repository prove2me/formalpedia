-- Prove2me | Theorems.Thm_GeneralPieces_Level_child_spec2
-- name    : GeneralPieces.Level.child_spec2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:39.794223+00:00
-- url     : https://prove2.me/theorems/d1624634-3c03-443a-b0f9-8a90b18f83a5
-- title:
--   Level: child spec2
-- statement:
--   One term of the sum over ι (a pattern, numbered y) whose network, on g = p nodes that are merged
--   rows or columns of e = d nodes, is rebalanced, by case (ii) of Lemma 8: the new instance has the
--   value of the
--   network and is well formed.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Level.lean#L80-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Level.lean#L80-L94

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

theorem GeneralPieces.Level.child_spec2 (P : PiecesF) (pad : U) (s : Step) (lam B : ℕ) (I : PInst) (y : ℕ) (hL : LevelOK2 P s lam) (hlam : I.1.length = lam)
    (hb : BudG P pad.length s lam) (hy : y < nPat P s lam) (hc : (s.thin && colSide P s lam y) = false) (g e : ℕ) (hg : g = s.p) (he : e = s.d)
    (N : Network (Fin g) (List Bool) (List Bool))
    (hN : (gridF P).toP.Presents (gctx pad s (!s.thin && colSide P s lam y) I y) N 0 0)
    (hS : N.Sized (P.m * (g * e ^ 2 * lam)) (e * B + e ^ 2 * P.bits s.h lam))
    (hU : N.U = totalG P s.p s.d (!s.thin && colSide P s lam y) s.h lam y)
    (hM : ∀ a b, a ≠ b → N.c a b ≤ e ^ 2 * (P.m * lam)) :
    ∃ J, childG P pad s I y = some J ∧ zval s.K J = N.value ∧ WFe s.K (lamNextG P s lam) (bNextG P s lam B) J := by sorry
