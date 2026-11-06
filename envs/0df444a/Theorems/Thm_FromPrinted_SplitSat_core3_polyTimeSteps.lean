-- Prove2me | Theorems.Thm_FromPrinted_SplitSat_core3_polyTimeSteps
-- name    : FromPrinted.SplitSat.core3_polyTimeSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:41:26.588173+00:00
-- url     : https://prove2.me/theorems/cf7c9ba0-9998-4c9f-a5d3-a86af9c7048f
-- title:
--   Split Sat: core3 poly Time Steps
-- statement:
--   The steps of `core3 ℓ τ` are polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Core.lean#L49-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Core.lean#L49-L65

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

theorem FromPrinted.SplitSat.core3_polyTimeSteps (ℓ τ : ℕ) : PolyTimeSteps (core3 ℓ τ) := by sorry
