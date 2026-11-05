-- Prove2me | Theorems.Thm_Groundwork_brute_runs_pow
-- name    : Groundwork.brute_runs_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:33.098386+00:00
-- url     : https://prove2.me/theorems/774e5faa-61da-442f-860c-a930aa63d650
-- title:
--   Groundwork: brute runs pow
-- statement:
--   The same with |R| ≤ 2^B and the size bound written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean#L137-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Brute.lean#L137-L147

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

theorem Groundwork.brute_runs_pow {K : ℕ} {lam : C → ℕ} {dflt : C → List Bool}
    {R : Stepped (C × ℕ × List (List Bool)) ℤ} {c : C} (Rm : Inst (Fin K) (List Bool)) (t S B : ℕ)
    (hR : ∀ (v : Fin K) (θ : Fin K → List Bool), (∀ u, u ≠ v → (θ u).length = lam c) → θ v = dflt c →
      R.Runs (c, v.1, List.ofFn θ) t S (Rm v θ) ∧ (Rm v θ).natAbs ≤ 2 ^ B) :
    (brute K lam dflt R).Runs c (2 ^ (K * (K - 1) / 2 * lam c) * (K * (t + 1) + 1))
      (2 * size c + 3 * (K * (K - 1) / 2 * lam c) + 2 * (B * K) + size K + S + 10)
      (Inst.ZW (lam c) (dflt c) Rm) := by sorry
