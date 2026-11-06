-- Prove2me | Theorems.Thm_FromPrinted_SplitSat_core3_decides
-- name    : FromPrinted.SplitSat.core3_decides
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:42:32.157794+00:00
-- url     : https://prove2.me/theorems/ec273434-e2d4-4985-ab8c-aece3da53e61
-- title:
--   Split Sat: core3 decides
-- statement:
--   If `Printed.SAT ℓ τ` decides 3-SAT on codes within c·2^{δn} steps, then `core3 ℓ τ` decides
--   3-SAT on pairs (N in unary, formula) with the exponent δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Core.lean#L69-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Core.lean#L69-L90

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

theorem FromPrinted.SplitSat.core3_decides {ℓ τ : ℕ} {δ : ℝ} (h : Paper.DecidesInSteps (Printed.SAT ℓ τ) δ) : ∃ c : ℕ, Decides3 (core3 ℓ τ) δ c := by sorry
