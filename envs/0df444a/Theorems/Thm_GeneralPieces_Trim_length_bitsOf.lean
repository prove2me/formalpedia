-- Prove2me | Theorems.Thm_GeneralPieces_Trim_length_bitsOf
-- name    : GeneralPieces.Trim.length_bitsOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:22:42.787276+00:00
-- url     : https://prove2.me/theorems/130037b3-76a7-4746-925c-465c3f977ec6
-- title:
--   Trim: length bits Of
-- statement:
--   The Trim construction uses the length bits Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Prog.lean#L30-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Trim/Prog.lean#L30-L30

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

theorem GeneralPieces.Trim.length_bitsOf {n : ℕ} (x : Pieces.Bits n) : (bitsOf x).length = n := by sorry
