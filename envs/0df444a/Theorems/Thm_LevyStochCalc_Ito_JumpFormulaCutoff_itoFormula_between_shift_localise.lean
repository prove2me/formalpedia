-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormulaCutoff_itoFormula_between_shift_localise
-- name    : LevyStochCalc.Ito.JumpFormulaCutoff.itoFormula_between_shift_localise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:32:27.479279+00:00
-- url     : https://prove2.me/theorems/f569096b-816b-4c1d-9e09-786e4a4dbae3
-- title:
--   itoFormula between shift localise
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormulaCutoff.itoFormula_between_shift_localise` is extracted from `LevyStochCalc.Ito.JumpFormulaCutoffLocalise`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaIncrement_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The increment formula for a translated path with no bound on the derivatives

The family of events on which a translated path stays in a ball over a bounded window exhausts
the sample space, and on the `m`-th member a twice continuously differentiable function agrees
with its box cutoff of radius `m + 1` along the translated path, together with its first two
derivatives. Transferring the increment formula for the cutoff along that family therefore gives
Itô's formula for the increment of the translated path between two ordered stopping times, with
no bound on the derivatives of the function and none on the translation; the stochastic terms
are matched there by hypothesis, from a stopping time below which the two integrands agree.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormulaCutoff

universe u

section Localise

open LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

set_option maxHeartbeats 1000000 in
-- the localisation case split against the shifted, translated coefficients elaborates a large
-- number of nested `nlinarith`/`linarith` goals and needs more than the default budget.

theorem _root_.LevyStochCalc.Ito.JumpFormulaCutoff.itoFormula_between_shift_localise
    (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (W.W k) ℱ')
    {X : ℝ → Ω → Fin n → ℝ} (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {bdrift : Fin n → Ω → ℝ → ℝ}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {T : ℝ}
    {c : Ω → Fin n → ℝ} (hc : Measurable c)
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
    (S : ℕ → Set Ω) (hScover : ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ S m)
    (hSball : ∀ (m : ℕ) (ω : Ω), ω ∈ S m → ∀ s : ℝ, σ ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) ≤ τ ω → ‖X s ω + c ω‖ ≤ (m : ℝ))
    (hSend : ∀ (m : ℕ) (ω : Ω), ω ∈ S m →
      ‖X (clipTime τ T ω) ω + c ω‖ ≤ (m : ℝ) ∧ ‖X (clipTime σ T ω) ω + c ω‖ ≤ (m : ℝ))
    (hSI : ∀ (m : ℕ) (p : Fin n) (k : Fin d)
      (hmg : Measurable (Function.uncurry fun ω s =>
        Probability.stopped τ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s))
      (hpg : Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s)
      (hqg : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s
            - Probability.stopped σ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                  * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      ∀ᵐ ω ∂P, ω ∈ S m →
        stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ (fun ω s =>
                  coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                    * H p k ω s) ω s
                - Probability.stopped σ (fun ω s =>
                    coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                      * H p k ω s) ω s)
            hmg hpg hqg T ω
          = stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
            (hmSc p k) (hpSc p k) (hqSc p k) T ω)
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
