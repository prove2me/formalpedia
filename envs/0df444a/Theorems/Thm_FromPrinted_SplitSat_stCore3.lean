-- Prove2me | Theorems.Thm_FromPrinted_SplitSat_stCore3
-- name    : FromPrinted.SplitSat.stCore3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:01:18.58501+00:00
-- url     : https://prove2.me/theorems/6a569957-ffd6-44e4-a919-f2de4f480fb3
-- title:
--   Split Sat: st Core3
-- statement:
--   **Theorem 2 gives s_3 = 0**, for the machine of Theorem 2 in its decision form without its
--   reader: for every δ > 0 there are ℓ and τ such that `core3 ℓ τ` has polynomial-time steps and
--   decides 3-SAT with the exponent δ. This is the statement `FromPrinted.SplitSat.StCore3`; ℓ and τ are
--   those of `Printed.stDecides`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Core.lean#L96-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Core.lean#L96-L98

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

theorem FromPrinted.SplitSat.stCore3 : StCore3 := by sorry
