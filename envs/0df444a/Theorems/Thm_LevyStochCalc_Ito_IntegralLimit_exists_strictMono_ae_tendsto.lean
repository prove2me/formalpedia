-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_IntegralLimit_exists_strictMono_ae_tendsto
-- name    : LevyStochCalc.Ito.IntegralLimit.exists_strictMono_ae_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T07:47:48.568145+00:00
-- url     : https://prove2.me/theorems/ee3141cd-19c4-4194-8040-ccb7e25956d1
-- title:
--   exists strictMono ae tendsto
-- statement:
--   The source theorem `LevyStochCalc.Ito.IntegralLimit.exists_strictMono_ae_tendsto` is extracted from `LevyStochCalc.Ito.StochasticIntegralLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaRandomShift_F001
import Definitions.Def_LevyStochCalc_Poisson_SmallJump_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Limits of stochastic integrals along dominated sequences of integrands

A sequence of integrands converging pointwise almost everywhere and dominated by a
square-integrable function converges to its limit in the energy norm, over `P ⊗ ds` for a
Brownian integrand and over `P ⊗ ds ⊗ ν` for a marked one. Through the `L²` isometries of the
Itô and compensated Itô–Lévy integrals this transfers to the integrals themselves: they converge
in `L²`, hence almost surely along a subsequence.

## Main statements

All statements live in the `LevyStochCalc.Ito.IntegralLimit` namespace.

* `tendsto_lintegral_sq_sub_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds`.
* `tendsto_lintegral_sq_sub_mark_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds ⊗ ν`.
* `tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated` and
  `exists_seq_ae_tendsto_stochasticIntegralBrownian_of_dominated` — the Itô integrals of a
  dominated sequence of integrands converge in `L²`, and almost surely along a strictly monotone
  subsequence.
* `tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated` and
  `exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated` — the same for the
  compensated Itô–Lévy integral.
* `tendsto_lintegral_sq_stochasticIntegral_markCut_compl` and
  `exists_seq_ae_tendsto_stochasticIntegral_markCut_compl` — the compensated Itô–Lévy integrals
  of an integrand cut to the complements of a family of mark sets that eventually misses almost
  every mark converge to the compensated Itô–Lévy integral of the integrand; the suffix
  `_of_antitone` names the same conclusions under an antitone family with null intersection.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.4 (Thm 4.4.7).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.IntegralLimit

universe u v

section Basic

variable {α : Type*} [MeasurableSpace α]

end Basic

section Unmarked

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

end Unmarked

section Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]

end Marked

section Subsequence

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

theorem _root_.LevyStochCalc.Ito.IntegralLimit.exists_strictMono_ae_tendsto {u : ℕ → Ω → ℝ} {v : Ω → ℝ} {ms : ℕ → ℕ}
    (hms : ∀ i : ℕ, i ≤ ms i)
    (h : ∀ᵐ ω ∂P, Tendsto (fun i => u (ms i) ω) atTop (𝓝 (v ω))) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i : ℕ, i ≤ k i) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u (k i) ω) atTop (𝓝 (v ω)) := by sorry
