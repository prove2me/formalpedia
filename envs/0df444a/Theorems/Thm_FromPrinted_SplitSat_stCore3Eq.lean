-- Prove2me | Theorems.Thm_FromPrinted_SplitSat_stCore3Eq
-- name    : FromPrinted.SplitSat.stCore3Eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:05:47.537866+00:00
-- url     : https://prove2.me/theorems/748820db-1d7f-4e03-82b7-86ba5a412f0e
-- title:
--   Split Sat: st Core3 Eq
-- statement:
--   The machine of Theorem 2 is the reader of the input followed by `core3`: the statement
--   `FromPrinted.SplitSat.StCore3Eq`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Core.lean#L46-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Core.lean#L46-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_Printed_End
import Definitions.Def_Printed_Count
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_Exits_Poly
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_WidthK_Top_Poly
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Core
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify WidthK.Prog UniformInK Paper CountKSat Eight Eight.ViaGrouping GraphProblems SplitSat
open FromPrinted FromPrinted.SplitSat

theorem FromPrinted.SplitSat.stCore3Eq : StCore3Eq := by sorry
