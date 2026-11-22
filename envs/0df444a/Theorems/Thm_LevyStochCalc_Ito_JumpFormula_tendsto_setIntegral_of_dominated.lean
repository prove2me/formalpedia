-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_tendsto_setIntegral_of_dominated
-- name    : LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:37:15.946893+00:00
-- url     : https://prove2.me/theorems/c164699c-f96f-4db4-977c-033915699ec5
-- title:
--   tendsto setIntegral of dominated
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated` is extracted from `LevyStochCalc.Ito.JumpFormulaLimit`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The small-jump limit of the Itô–Lévy formula

The finite-activity Itô–Lévy formula applies to a jump diffusion whose jump coefficient is cut to
a set of marks. Along a family `A : ℕ → Set E` of small-jump sets with `ν`-null intersection the
cut coefficients restore the original ones, and the formula is passed to the limit term by term:
the increment of the state function and the drift, diffusion and compensated jump terms converge
along the truncated paths, and the compensator-drift term converges by dominated convergence on
the product of the time window with the intensity. The identity of the limits is then the
uniqueness of the limit of a real sequence, read on the two sides of the formula.

Cutting the jump coefficient to a set of marks leaves the drift integrand `∂_t u + 𝓛u` unchanged
— it reads only `μ` and `σ` — and turns the compensator-drift integrand into its restriction to
that set. The two presentations of the drift differ by the first-order term `∑ᵢ ∂ᵢu ∫ γᵢ dν`,
which is finite only when the jump coefficient is `ν`-integrable: for a jump coefficient that is
merely square-integrable near the small marks, the first-order term and the mark integral of the
jump increment `u(x + γ) − u(x)` each diverge and only their difference, the compensator-drift
integrand `u(x + γ) − u(x) − γᵀ∇u`, is integrable. The limit statements below are therefore
carried by the compensator-drift integrand; the first-order term is passed to the limit
separately only under an integrability hypothesis on the jump coefficient itself.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.markTruncCoeffs` — the coefficient bundle with the jump
  coefficient cut to a set of marks.
* `LevyStochCalc.Ito.JumpFormula.firstOrderIntegrand` — the first-order term `∑ᵢ γᵢ ∂ᵢu` of the
  compensator-drift integrand.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_of_antitone`,
  `LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_comp` — almost every mark eventually lies
  outside an antitone family of mark sets with null intersection, also along a subsequence.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated` — dominated convergence for
  the mark integral over the complements of the family, integrated over a time window.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_compensatorDrift` — the compensator-drift
  integrals over the complements of the family converge to the compensator-drift integral over
  the whole mark space along the limit path.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_firstOrder` — the same for the first-order
  term, under integrability of the jump coefficient against the intensity.
* `LevyStochCalc.Ito.JumpFormula.driftIntegrand_markTruncCoeffs`,
  `LevyStochCalc.Ito.JumpFormula.integral_compensatorDriftIntegrand_markTruncCoeffs` — cutting
  the jump coefficient leaves the drift integrand unchanged and restricts the compensator-drift
  integral to the cut.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_sub_of_markTruncCoeffs` — the Itô–Lévy identity for cut
  coefficients, in the vocabulary of the uncut ones.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_tendsto`,
  `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto` — the two sides of an identity of
  real sequences have equal limits, pointwise and almost surely.
* `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto_terms` — the Itô–Lévy identity along
  the limit path, from the identities along the truncated paths with the drift and
  compensator-drift terms given as arbitrary sequences, and the convergence of the five terms.
* `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto_integrals` — the same with the drift
  and compensator-drift terms given as the integrals along the truncated paths, the latter over
  the complements of the truncated mark sets.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., 2009, Theorem 4.4.7, step (II).
-/

open MeasureTheory Filter Topology
open LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section MarkSets

variable {E : Type v} [MeasurableSpace E] {ν : Measure E}

end MarkSets

section Dominated

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

theorem _root_.LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated
    {T : ℝ} {A : ℕ → Set E} {fs : ℕ → ℝ → E → ℝ} {f g : ℝ → E → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hev : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m)
    (hmeas : ∀ m, AEStronglyMeasurable (fun p : ℝ × E => fs m p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hg : Integrable (fun p : ℝ × E => g p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hdom : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e, |fs m s e| ≤ g s e)
    (hconv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e, Tendsto (fun m => fs m s e) atTop (𝓝 (f s e))) :
    Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν)) := by sorry
