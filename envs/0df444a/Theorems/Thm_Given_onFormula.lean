-- Prove2me | Theorems.Thm_Given_onFormula
-- name    : Given.onFormula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:56:15.882723+00:00
-- url     : https://prove2.me/theorems/2e44a48f-0da1-4a32-99f0-82ec22a93b8a
-- title:
--   Given: on Formula
-- statement:
--   **Lemma 1, applied to the network of Φ.** If NM does what Lemma 1 says for (K, e) on networks on
--   [g], then NM, with its queries answered by the procedures of the network of Φ, returns the value Z
--   of that network within C·2^{eU + (e+2)·gP/K}·(P + 1)^C steps: B = 1 and τ = 1. The bounds are
--   written as in `Eight.ViaGrouping.Correct.onFormula`; C = 3C₁ + 5 (the 3 is that of `StOnGiven`).
--   With it, in one conclusion: the machine has polynomial-time steps if NM has. The text is that of
--   `Printed.onFormula`, with `stFormulaGiven` and `stOnGiven` (read by `onSteps`) in the places of
--   `Printed.formula_isNetwork` and `Printed.stOnProcedures`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/End.lean#L56-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/End.lean#L56-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Eight_ViaGrouping_Correct_onFormula
import Theorems.Thm_Printed_onFormula

set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

theorem Given.onFormula {NM : NetMachine} {C₁ g K : ℕ} {e : ℝ} (hg : 0 < g) (k : ℕ) (h : ComputesNetworks NM C₁ g K e) :
    (NM.PolyTimeSteps → Nonempty (IsPolyT (networkOnSteps g NM (formulaProcs g k)))) ∧ ∃ C : ℕ, ∀ Φ : Fml, ∃ T : ℕ,
      (networkOnSteps g NM (formulaProcs g k)).Runs Φ T (size Φ + 2 * g + 6 * (mu g Φ * k) + 10 + C * (size Φ + satPf g k Φ + 1) ^ C) (wordNet g k Φ).value ∧
      (T : ℝ) ≤ C * (2 : ℝ) ^ (e * ((wordNet g k Φ).U : ℝ) + (e + 2) * ((g : ℝ) * (satPf g k Φ : ℝ)) / K) * ((satPf g k Φ : ℝ) + 1) ^ C := by sorry
