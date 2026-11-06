-- Prove2me | Theorems.Thm_Given_onSteps
-- name    : Given.onSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:34:18.918407+00:00
-- url     : https://prove2.me/theorems/917c5bd2-6613-48da-8102-870a0fd54221
-- title:
--   Given: on Steps
-- statement:
--   `stOnGiven` for procedures that are step machines: polynomial-time steps of the step machine
--   `networkOnSteps g NM Np` and the number of its steps, in one conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Networks.lean#L93-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Networks.lean#L93-L102

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

theorem Given.onSteps {NM : NetMachine} {C₁ g K : ℕ} {e : ℝ} (hNM : ComputesNetworks NM C₁ g K e) [HasSize C] [Enc C] [Carried C] {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
    (h : IsGivenNetwork (ofProcs Np) noTable c N P B τ S) :
    (NM.PolyTimeSteps → Nonempty (IsPolyT (networkOnSteps g NM Np))) ∧
    ∃ T : ℕ, (networkOnSteps g NM Np).Runs c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
      (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ := by sorry
