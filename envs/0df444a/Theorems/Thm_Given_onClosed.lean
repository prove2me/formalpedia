-- Prove2me | Theorems.Thm_Given_onClosed
-- name    : Given.onClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:29:37.356196+00:00
-- url     : https://prove2.me/theorems/05abb71c-f4db-4ad2-801e-3094b73eaaa2
-- title:
--   Given: on Closed
-- statement:
--   `stOnGiven`, the count of operations, read for the step machine with the oracle built in.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Networks.lean#L82-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Networks.lean#L82-L89

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

theorem Given.onClosed {NM : NetMachine} {C₁ g K : ℕ} {e : ℝ} (hNM : ComputesNetworks NM C₁ g K e) [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] {Np : ProcsQ Q A C} {O : Q → Option A} {c : C} {N : Net g} {P B τ S : ℕ}
    (h : IsGivenNetwork Np O c N P B τ S) :
    ∃ T : ℕ, (networkOnSteps g NM (Np.close O)).Runs c T (size c + C₁ * (P + B) ^ C₁ + S + 4) N.value ∧
      (T : ℝ) ≤ 3 * (C₁ * (2 : ℝ) ^ (e * ((N.U : ℝ) + (g : ℝ) * P / K) + 2 * ((g : ℝ) * P) / K) * ((P : ℝ) + B) ^ C₁) * τ := by sorry
