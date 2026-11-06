-- Prove2me | Theorems.Thm_Given_networkOn_steps
-- name    : Given.networkOn_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:34:54.602445+00:00
-- url     : https://prove2.me/theorems/2ccb42ee-3381-48d9-b136-7b158a8b0016
-- title:
--   Given: network On steps
-- statement:
--   A machine for networks with polynomial-time steps, on procedures with polynomial-time steps: the
--   second conjunct of `IsGivenNetwork` is all that is used. (`stOnGiven` says the same of a network;
--   here no network is at hand, since g, K and M are arbitrary.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean#L290-L291
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean#L290-L291

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Networks
import Definitions.Def_Printed_End
import Mathlib.Tactic
import Definitions.Def_Given_Level
set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed

theorem Given.networkOn_steps {Q A C : Type} [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] (g : ℕ) (NM : NetMachine) (Np : ProcsQ Q A C) (hN : NM.PolyTimeSteps) (h : PolyTimeProcs Np) : (networkOn g NM Np).PolyTimeSteps := by sorry
