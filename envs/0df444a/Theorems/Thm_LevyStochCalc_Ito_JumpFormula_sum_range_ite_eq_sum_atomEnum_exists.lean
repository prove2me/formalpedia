-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_sum_range_ite_eq_sum_atomEnum_exists
-- name    : LevyStochCalc.Ito.JumpFormula.sum_range_ite_eq_sum_atomEnum_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:08:41.478649+00:00
-- url     : https://prove2.me/theorems/2395ae4a-30fb-40cd-885c-30b3edb64dfe
-- title:
--   sum range ite eq sum atomEnum exists
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.sum_range_ite_eq_sum_atomEnum_exists` is extracted from `LevyStochCalc.Ito.JumpFormulaFiniteActivityExhaustion`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaFiniteActivityExhaustion_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Exhausting a finite-activity jump path by its arrival times

The jumps of a mark set accumulated up to the arrival times capped at the horizon no longer move
once the arrival time has passed the horizon, so a telescope over a chain of arrival times has
only in-window terms, and the in-window members of such a chain are matched one for one with the
entries of the strictly monotone enumeration of the window's atom times. On a mark set of finite
intensity almost every path has an arrival time beyond the horizon, so an identity holding almost
everywhere on each event where the chain has passed the horizon holds almost everywhere. Between
consecutive arrival times inside the window the accumulated jumps gain exactly the jump
coefficient carried by the later arrival time and the mark enumerated with it, and the progressive
measurability of the chain data and of the integrands passes to the right-continuous
regularisation of a filtration.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section CappedShift

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) (A : Set E)

end CappedShift

section Reindex

theorem _root_.LevyStochCalc.Ito.JumpFormula.sum_range_ite_eq_sum_atomEnum_exists {K m : ℕ} {θ : Fin K → ℝ} {σ : ℕ → WithTop ℝ}
    {T : ℝ} (hθ : StrictMono θ) (hmemθ : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, σ i = ((v : ℝ) : WithTop ℝ) ∧ 0 < v ∧ v ≤ T})
    (hσmono : Monotone σ) (hσ0 : σ 0 = ((0 : ℝ) : WithTop ℝ))
    (hstrict : ∀ i : ℕ, σ (i + 1) ≤ ((T : ℝ) : WithTop ℝ) → σ i < σ (i + 1))
    (hm : ((T : ℝ) : WithTop ℝ) ≤ σ m) (G' : ℕ → ℝ) (G : Fin K → ℝ)
    (hex : ∀ k : ℕ, σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) →
      ∃ j : Fin K, σ (k + 1) = ((θ j : ℝ) : WithTop ℝ) ∧ G' k = G j) :
    (∑ k ∈ Finset.range m,
        if σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) then G' k else 0)
      = ∑ j : Fin K, G j := by sorry
