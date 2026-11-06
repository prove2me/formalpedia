-- Prove2me | Theorems.Thm_OccurM_boundInClausesTied
-- name    : OccurM.boundInClausesTied
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:14:20.744429+00:00
-- url     : https://prove2.me/theorems/46d94154-34de-4bc4-aaa9-5810b8d088c0
-- title:
--   Occur M: bound In Clauses Tied
-- statement:
--   The bound in m of the Main Theorem for the named programs, on programs for the pieces of
--   Appendix B; α' = log √2 = ½.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L59-L64
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L59-L64

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

theorem OccurM.boundInClausesTied : BoundInClausesTied := by sorry
