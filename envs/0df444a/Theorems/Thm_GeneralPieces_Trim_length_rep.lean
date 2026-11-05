-- Prove2me | Theorems.Thm_GeneralPieces_Trim_length_rep
-- name    : GeneralPieces.Trim.length_rep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:21:54.058248+00:00
-- url     : https://prove2.me/theorems/eb3e6e61-0755-4ea2-8c77-90e2e4813b84
-- title:
--   Trim: length rep
-- statement:
--   The Trim construction uses the length rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Prog.lean#L32-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Prog.lean#L32-L32

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

theorem GeneralPieces.Trim.length_rep (n : ℕ) : (rep n).length = n := by sorry
