-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_itoFormula_between_generalShift_localise
-- name    : LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift_localise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:12:15.787425+00:00
-- url     : https://prove2.me/theorems/8099797d-7bed-4ecd-b540-307a16d8f7d7
-- title:
--   itoFormula between generalShift localise
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift_localise` is extracted from `LevyStochCalc.Ito.ItoFormulaLocalised`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGeneralShift_F000
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGeneralShift_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The increment formula with a random shift and no bound on the derivatives

Multiplying a twice continuously differentiable function by a smooth box cutoff of radius `R`
leaves the function and its first two derivatives unchanged on the ball of radius `3R/2` and
makes those derivatives globally bounded. A path that has not left the ball of radius `j`,
translated by a shift of norm at most `M`, stays inside that ball as soon as `R = j + M`, so the
increment formula for the cutoff carries the same integrands as the increment formula for the
function; the stochastic terms are matched by the local property of the Itô integral at the exit
time of the path, and letting `j` grow exhausts almost every sample point.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift_localise` — the increment formula
  between two stopping times for a function translated by a bounded random vector, deduced from
  the same formula for functions whose first two derivatives are globally bounded.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Localise

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

theorem _root_.LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift_localise
    {X : ℝ → Ω → Fin n → ℝ} (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (hXc : ∀ ω, Continuous fun s => X s ω)
    (hXa : MeasureTheory.Adapted ℱ' fun r ω => X r ω)
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {bdrift : Fin n → Ω → ℝ → ℝ}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω) (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {T : ℝ} (hT : 0 < T)
    {c : Ω → Fin n → ℝ} (hc : Measurable c) {M : ℝ} (hcb : ∀ ω, ‖c ω‖ ≤ M)
    (hmSc : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSc : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSc : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hpShift : ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → ∀ (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ (fun ω s => φ (X s ω + c ω) * H p k ω s) ω s
          - Probability.stopped σ (fun ω s => φ (X s ω + c ω) * H p k ω s) ω s)
    (hbase : ∀ (g : (Fin n → ℝ) → ℝ) (g' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
      (g'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (K₁ K₂ : ℝ),
      ContDiff ℝ 2 g → (∀ z, HasFDerivAt g (g' z) z) → (∀ z, HasFDerivAt g' (g'' z) z) →
      (∀ (p : Fin n) (z : Fin n → ℝ), |coordDeriv g' p z| ≤ K₁) →
      (∀ (p q : Fin n) (z : Fin n → ℝ), |coordDeriv₂ g'' p q z| ≤ K₂) →
      ∀ (hmSg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
          Probability.stopped τ
              (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s))
        (hpSg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
          Probability.stopped τ
              (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s)
        (hqSg : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖Probability.stopped τ
                  (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s‖₊
              : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      (fun ω : Ω => g (X (clipTime τ T ω) ω + c ω) - g (X (clipTime σ T ω) ω + c ω))
        =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ
                (fun ω s => coordDeriv g' p (X s ω + c ω) * bdrift p ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv g' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped τ
                      (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
                    - Probability.stopped σ
                        (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s)
                (hmSg p k) (hpSg p k) (hqSg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped τ (fun ω s => coordDeriv₂ g'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped σ (fun ω s => coordDeriv₂ g'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c ω) - f (X (clipTime σ T ω) ω + c ω))
      =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped τ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped σ
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
              (hmSc p k) (hpSc p k) (hqSc p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by sorry
