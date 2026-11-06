-- Prove2me | Theorems.Thm_OccurM_countsFromPiecesTied
-- name    : OccurM.countsFromPiecesTied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:08:17.755198+00:00
-- url     : https://prove2.me/theorems/bf53ac9d-1b21-4804-a82d-f24823be1809
-- title:
--   Occur M: counts From Pieces Tied
-- statement:
--   Theorem A (c), first sentence, for the named programs: the preparation, then the top level in m
--   on the recursion of part (b).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L54-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L54-L55

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_GeneralPieces_Main
import Definitions.Def_GeneralPieces_Tied_Bound
import Definitions.Def_GeneralPieces_Num_PartD
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_OccurM_Main
set_option autoImplicit false
section
section
open OccurM
open Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Turing MainTheoremForms ClausesOccur

theorem OccurM.countsFromPiecesTied : CountsFromPiecesTied := by sorry
