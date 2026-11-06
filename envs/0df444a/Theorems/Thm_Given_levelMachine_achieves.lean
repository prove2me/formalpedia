-- Prove2me | Theorems.Thm_Given_levelMachine_achieves
-- name    : Given.levelMachine_achieves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:35:17.569841+00:00
-- url     : https://prove2.me/theorems/b252e7b3-2b8e-49cb-b658-aa269418b8d2
-- title:
--   Given: level Machine achieves
-- statement:
--   «Cost» for `levelMachine`: if the machine of Lemma 1 does what Lemma 1 says on networks on [g],
--   then `levelMachine K g M` does what `Printed.AchievedBy` asks for (g², (ρ + 2/K)e + 2/K).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean#L263-L270
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean#L263-L270

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

theorem Given.levelMachine_achieves {K g C₁ : ℕ} {e : ℝ} {M : CliqueMachine} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e)
    (hNM : ComputesNetworks (groupingMachine K g M) C₁ g K e) : ∃ Cc' : ℕ, AchievedBy (levelMachine K g M) Cc' (g * g) ((rho + 2 / K) * e + 2 / K) := by sorry
