-- Prove2me | Theorems.Thm_GeneralPieces_Level_cases_ii
-- name    : GeneralPieces.Level.cases_ii
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:44.122064+00:00
-- url     : https://prove2.me/theorems/20e2882d-b797-4252-b935-3f8c836c2847
-- title:
--   Level: cases ii
-- statement:
--   "Case (ii) of the lemma applies to the network with the smaller total": K divides g, c_{a,a'} ≤
--   g²λ = P/g, and 2ζ²g ≥ K·ln(2gK). Here the network has p nodes, each a merged row or column of d
--   nodes,
--   its parameter is P = m·p·d²·λ, and two nodes share at most d²·m·λ = P/p bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Level.lean#L41-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Level.lean#L41-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Level
import Definitions.Def_GeneralPieces_Rec_Level
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Level
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.Level Finset

theorem GeneralPieces.Level.cases_ii {P : PiecesF} {s : Step} {lam : ℕ} (hL : LevelOK2 P s lam) (N : Network (Fin s.p) (List Bool) (List Bool))
    (hM : ∀ a b, a ≠ b → N.c a b ≤ s.d ^ 2 * (P.m * lam)) : AppRunningTime.Cases s.K s.p (zetaOf s) (P.m * (s.p * s.d ^ 2 * lam)) N.c := by sorry
