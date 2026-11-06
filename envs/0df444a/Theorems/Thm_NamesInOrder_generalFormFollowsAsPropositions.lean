-- Prove2me | Theorems.Thm_NamesInOrder_generalFormFollowsAsPropositions
-- name    : NamesInOrder.generalFormFollowsAsPropositions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:15:21.852755+00:00
-- url     : https://prove2.me/theorems/85190768-741e-4912-9a32-675669be4415
-- title:
--   Names In Order: general Form Follows As Propositions
-- statement:
--   So the Main Theorem with nothing added to the bound, for formulas whose variables all occur,
--   gives the Main Theorem for formulas with any names, with a polynomial in the length of the code
--   added.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/General.lean#L63-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/General.lean#L63-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Main
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_Wrap_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_NamesInOrder_General
set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork Wrap TwoMachines MainTheoremForms MinOfBounds
open Sat3 (CNF)

theorem NamesInOrder.generalFormFollowsAsPropositions : GeneralFormFollowsAsPropositions := by sorry
