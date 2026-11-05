-- Prove2me | Theorems.Thm_GeneralPieces_Level_Lof_le_lamNext
-- name    : GeneralPieces.Level.Lof_le_lamNext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:57.050587+00:00
-- url     : https://prove2.me/theorems/e187f134-8eaa-4898-be88-b8bbc0c00d6d
-- title:
--   Level: Lof le lam Next
-- statement:
--   "The number L depends on ι; the bound holds for every ι": the lemma's L = ⌈(U + 2ζgP)/K²⌉ is at
--   most the label length `lamNextG` that the program uses for all ι, if U is at most the bound
--   `ubarG` for the smaller total.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Level.lean#L54-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Level.lean#L54-L72

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

theorem GeneralPieces.Level.Lof_le_lamNext {P : PiecesF} {s : Step} {lam : ℕ} (hL : LevelOK2 P s lam) (Uv : ℕ) (hU : Uv ≤ ubarG P s lam) :
    AppRunningTime.Lof s.K s.p (zetaOf s) (P.m * (s.p * s.d ^ 2 * lam)) Uv ≤ lamNextG P s lam := by sorry
