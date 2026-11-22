-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_setIntegral_splitDrift_dictionary_mixed
-- name    : LevyStochCalc.Ito.JumpFormula.setIntegral_splitDrift_dictionary_mixed
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:41:16.498474+00:00
-- url     : https://prove2.me/theorems/af9510bc-c26a-4aca-9ac0-5aec0f68ba42
-- title:
--   setIntegral splitDrift dictionary mixed
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.setIntegral_splitDrift_dictionary_mixed` is extracted from `LevyStochCalc.Ito.JumpFormulaMixedDictionary`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaMixedDictionary_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The split-drift dictionary for the mixed integrands

Splitting a finite-activity jump diffusion into a continuous Itô part and a pathwise jump sum
replaces the drift `μ` by `μ` minus the compensator `∫_A γ dν` of the jumps, while the pathwise
jump sum contributes the intensity integral of the jump increment. Read with the derivatives of
the state function at a state `y` and the coefficients at a state `x`, the two presentations of
the drift differ by the first-order term `∑ᵢ ∂ᵢu(s, y) ∫_A γᵢ(s, x) dν`, which the compensator
subtracted from the drift supplies exactly.

The statements below are the mixed forms of the drift reconciliation, of the split-drift
dictionary in the coordinates with a time coordinate prepended, and of the Itô–Lévy identity
assembled from them; the assembled identity carries the compensator-drift term over the mark set
carrying the jump coefficient. At `y = x` they are the statements of
`LevyStochCalc.Ito.JumpFormulaFiniteActivity`.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedFirstOrder_eq`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedCompensatorDriftIntegrand_eq_sub` — the mark
  integral of the mixed compensator-drift integrand as the mark integral of the mixed jump
  increment minus the first-order term.
* `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedCompensatorDrift_eq_sub`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_firstOrder_add_mixedCompensatorDrift` — the drift
  reconciliation over a time window for the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.mixedDriftIntegrand_dictionary`,
  `LevyStochCalc.Ito.JumpFormula.splitDriftIntegrand_dictionary_mixed` — the non-stochastic
  integrands of Itô's formula in the prepended coordinates, with the derivatives at one state
  and the coefficients at another, as the mixed drift integrand and as the mixed drift integrand
  minus the first-order term.
* `LevyStochCalc.Ito.JumpFormula.splitDrift_pointwise_mixed`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_splitDrift_dictionary_mixed` — the same taken
  against a unit time drift, the drift with the jump compensator subtracted and a diffusion
  matrix whose time row vanishes, pointwise and integrated over a window.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed`,
  `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_of_support` — the
  Itô–Lévy identity for the mixed integrands from the split-drift identity and the jump-sum
  identity, with the compensator-drift term over the mark set and, for a jump coefficient
  carried by that set, over the whole mark space.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe v

section MixedDriftReconciliation

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

end MixedDriftReconciliation

section MixedSplitDrift

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

theorem _root_.LevyStochCalc.Ito.JumpFormula.setIntegral_splitDrift_dictionary_mixed (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (T : ℝ)
    (y x : ℝ → Fin n → ℝ) (b : Fin (n + 1) → ℝ → ℝ) (K : Fin (n + 1) → Fin d → ℝ → ℝ)
    (hb0 : ∀ s : ℝ, b 0 s = 1)
    (hbs : ∀ (q : Fin n) (s : ℝ),
      b q.succ s = coeffs.μ s (x s) q - ∫ e in A, coeffs.γ s (x s) e q ∂ν)
    (hK0 : ∀ (j : Fin d) (s : ℝ), K 0 j s = 0)
    (hKs : ∀ (p : Fin n) (j : Fin d) (s : ℝ), K p.succ j s = coeffs.σ s (x s) p j)
    (hD : ∀ p : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv f' p (Fin.cons s (y s)) * b p s) (Set.Ioc (0 : ℝ) T) volume)
    (hQ : ∀ p q : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv₂ f'' p q (Fin.cons s (y s)) * ∑ j : Fin d, K p j s * K q j s)
      (Set.Ioc (0 : ℝ) T) volume) :
    (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (Fin.cons s (y s)) * b p s ∂volume)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (Fin.cons s (y s))
              * ∑ j : Fin d, K p j s * K q j s ∂volume
      = ∫ s in Set.Ioc (0 : ℝ) T,
          (mixedDriftIntegrand u coeffs s (y s) (x s)
            - ∑ i : Fin n, gradient u s (y s) i
                * ∫ e in A, coeffs.γ s (x s) e i ∂ν) ∂volume := by sorry
