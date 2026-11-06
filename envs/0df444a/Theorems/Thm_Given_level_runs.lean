-- Prove2me | Theorems.Thm_Given_level_runs
-- name    : Given.level_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:34:50.883504+00:00
-- url     : https://prove2.me/theorems/417ff668-746f-455d-bc5c-233ba97db2e4
-- title:
--   Given: level runs
-- statement:
--   The paragraph «Cost» for the step machine that `levelMachine` becomes when the tables are built
--   in: value, number of steps, sizes. c holds λ and B in unary. The text is that of
--   `Printed.level_runs_of`, with `stGridGiven` in the place of `Printed.grid_isNetwork_of`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean#L111-L257
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/threesat/Given/Level.lean#L111-L257

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Networks
import Definitions.Def_Printed_End
import Mathlib.Tactic
import Definitions.Def_Given_Level
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine Printed

theorem Given.level_runs {K g C₁ : ℕ} {e : ℝ} {NM : NetMachine} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (hNM : ComputesNetworks NM C₁ g K e) :
    ∃ Cc' : ℕ, ∀ (c : List Unit × List Unit) (lam B : ℕ) (W : ℕ → List Bool → ℤ), c.1.length = lam → c.2.length = B → 1 ≤ lam → (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) →
      ∃ T : ℕ, (Stepped.bind (Stepped.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
            (Stepped.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOnSteps g NM ((gridProcs g false).close (tables (g * g) lam W))) (networkOnSteps g NM ((gridProcs g true).close (tables (g * g) lam W)))))
          (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ))).Runs c T (Cc' * (B + lam) ^ Cc') (Inst.ZW lam [] (listTables (g * g) W)) ∧
        (T : ℝ) ≤ Cc' * (2 : ℝ) ^ (((rho + 2 / K) * e + 2 / K) * (((g * g : ℕ) : ℝ)) ^ 2 * lam) * ((B : ℝ) + lam) ^ Cc' := by sorry
