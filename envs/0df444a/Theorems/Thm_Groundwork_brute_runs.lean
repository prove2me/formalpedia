-- Prove2me | Theorems.Thm_Groundwork_brute_runs
-- name    : Groundwork.brute_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:12:34.088207+00:00
-- url     : https://prove2.me/theorems/06df3bdf-e7ef-4c9a-9e25-fc2e98e3c1a4
-- title:
--   Groundwork: brute runs
-- statement:
--   `brute` computes Z in 2^(K(K-1)/2 · λ) · (K (t + 1) + 1) steps if R answers every query in t
--   steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean#L83-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean#L83-L134

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Range
import Definitions.Def_StepMachines_Prog_Chunks
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import Definitions.Def_StepMachines_Prog_Brute
set_option autoImplicit false
section
open Groundwork
open Finset Stepped
variable {C : Type} [HasSize C]

theorem Groundwork.brute_runs {K : ℕ} {lam : C → ℕ} {dflt : C → List Bool} {R : Stepped (C × ℕ × List (List Bool)) ℤ}
    {c : C} (Rm : Inst (Fin K) (List Bool)) (t S V : ℕ) (hV : 1 ≤ V)
    (hR : ∀ (v : Fin K) (θ : Fin K → List Bool), (∀ u, u ≠ v → (θ u).length = lam c) → θ v = dflt c →
      R.Runs (c, v.1, List.ofFn θ) t S (Rm v θ) ∧ (Rm v θ).natAbs ≤ V) :
    (brute K lam dflt R).Runs c (2 ^ (K * (K - 1) / 2 * lam c) * (K * (t + 1) + 1))
      (size c + size (2 ^ (K * (K - 1) / 2 * lam c)) + (size (2 ^ (K * (K - 1) / 2 * lam c) * V ^ K) +
        (size c + size (2 ^ (K * (K - 1) / 2 * lam c)) + size K + (size (V ^ K) + S) + 1)) + 1)
      (Inst.ZW (lam c) (dflt c) Rm) := by sorry
