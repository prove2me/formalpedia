-- Prove2me | Theorems.Thm_OccurM_everyWrapperCountsUnary
-- name    : OccurM.everyWrapperCountsUnary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:09:22.86091+00:00
-- url     : https://prove2.me/theorems/5d822710-59aa-4208-9bc1-4d2f29f732f5
-- title:
--   Occur M: every Wrapper Counts Unary
-- statement:
--   The same for the code that writes the number of variables in unary (`SatM.enc`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Wrapper.lean#L60-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/OccurM/Wrapper.lean#L60-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_OccurM_TiedDefs
import Definitions.Def_OccurM_Arith
import Definitions.Def_OccurM_Top
import Definitions.Def_OccurM_Wrapper
set_option autoImplicit false
section
section
open OccurM
open Groundwork Turing MainTheoremForms ClausesOccur
open Sat3 (CNF)

theorem OccurM.everyWrapperCountsUnary : EveryWrapperCountsUnary := by sorry
