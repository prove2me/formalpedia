-- Prove2me | Theorems.Thm_Given_ofProcs_poly
-- name    : Given.ofProcs_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:34:09.566196+00:00
-- url     : https://prove2.me/theorems/edc1fd04-4cff-4c9c-99d8-123d9e5d5f97
-- title:
--   Given: of Procs poly
-- statement:
--   Step machines with polynomial-time steps and numbers in unary, as procedures that ask nothing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Networks.lean#L33-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Networks.lean#L33-L38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GivenStatement
import Definitions.Def_Printed_LevelFrom
import Definitions.Def_Printed_Count
import Mathlib.Tactic
import Definitions.Def_Given_Networks
set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed
variable {Q A C : Type}

theorem Given.ofProcs_poly [Enc C] (Np : Procs C) (h : Np.Keeps) (hP : Unary Np.P) (hB : Unary Np.B) : PolyTimeProcs (ofProcs Np) := by sorry
