-- Prove2me | Theorems.Thm_OccurM_untie
-- name    : OccurM.untie
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:08:20.950097+00:00
-- url     : https://prove2.me/theorems/e54d34cd-1331-48e1-903b-400c69b2195b
-- title:
--   Occur M: untie
-- statement:
--   From the forms for the named programs (the tied forms: the machine is built from given programs
--   for the pieces) to the forms with «there is a machine»: the machine and the constant are those of
--   the field `machine`; x₀ is the least one of Theorem A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L69-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Main.lean#L69-L79

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

theorem OccurM.untie : UntieStmt := by sorry
