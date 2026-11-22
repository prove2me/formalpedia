-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_IntegralLimit_tendsto_lintegral_sq_sub_of_dominated
-- name    : LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_sq_sub_of_dominated
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T07:50:04.518817+00:00
-- url     : https://prove2.me/theorems/d7cbc407-2e85-4d71-b479-bff5b497c10c
-- title:
--   tendsto lintegral sq sub of dominated
-- statement:
--   The source theorem `LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_sq_sub_of_dominated` is extracted from `LevyStochCalc.Ito.StochasticIntegralLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F000

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

theorem _root_.LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_sq_sub_of_dominated {H : ℕ → Ω → ℝ → ℝ} {H₀ : Ω → ℝ → ℝ}
    {g : Ω → ℝ → ℝ} {T : ℝ}
    (hHm : ∀ m, Measurable (Function.uncurry (H m)))
    (hH₀m : Measurable (Function.uncurry H₀)) (hgm : Measurable (Function.uncurry g))
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => H m ω s) atTop (𝓝 (H₀ ω s)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ‖H m ω s‖ ≤ g ω s)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H m ω s - H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) atTop (𝓝 0) := by sorry
