-- Prove2me | Theorems.Thm_Given_stLevelPoly
-- name    : Given.stLevelPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:38:51.680426+00:00
-- url     : https://prove2.me/theorems/a5fea252-46ba-46a6-9030-12def5278f55
-- title:
--   Given: st Level Poly
-- statement:
--   The machine of Proposition 3 has polynomial-time steps if M has. The statement is
--   `Printed.StLevelPoly`; the text is that of `Printed.levelLoop_poly` and `Printed.stLevelPoly_of`,
--   with `gridProcs_poly`, the second conjunct of `stGridGiven`, for the two networks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean#L296-L305
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean#L296-L305

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Networks
import Definitions.Def_Printed_End
import Mathlib.Tactic
import Definitions.Def_Given_Level
import Theorems.Thm_Printed_stLevelPoly

set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed

theorem Given.stLevelPoly : StLevelPoly := by sorry
