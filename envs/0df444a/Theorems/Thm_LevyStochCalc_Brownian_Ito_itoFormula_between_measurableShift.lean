-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_itoFormula_between_measurableShift
-- name    : LevyStochCalc.Brownian.Ito.itoFormula_between_measurableShift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:24:38.213907+00:00
-- url     : https://prove2.me/theorems/8d896f52-18a1-4cbd-9aae-0d161028e2b6
-- title:
--   itoFormula between measurableShift
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.itoFormula_between_measurableShift` is extracted from `LevyStochCalc.Ito.ItoFormulaMeasurableShift`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGridShiftClosed_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula between two stopping times for a shift known at the earlier time

A random variable known at a stopping time, cut to the event that the time has already occurred by
a deterministic time, is measurable for the σ-algebra at that deterministic time; multiplying by
such a variable therefore preserves progressive measurability of a process that vanishes up to the
stopping time. Reading an integrand along a mark taking finitely many values splits the increment
of the integrand between two ordered stopping times over the values of the mark, so that increment
is progressively measurable as soon as the mark is known at the earlier time. The dyadic lattice
points below a bounded random vector known at the earlier stopping time form such marks and
converge to it, and truncating a random vector on the event that its norm exceeds a level produces
bounded vectors eventually equal to it, so Itô's formula for the increment holds for a shift that
is merely known at the earlier stopping time.

## Main statements

* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stoppingTimeWeight_mul` — a random variable
  known at a stopping time times a progressively measurable process vanishing up to that time is
  progressively measurable.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_of_measurableShift` — the
  increment between two ordered stopping times of an integrand read along a mark taking finitely
  many values and known at the earlier time is progressively measurable.
* `LevyStochCalc.Brownian.Ito.exists_simpleShift_approx_measurableSpace` — a bounded random vector
  known at a stopping time is a pointwise limit of random vectors taking finitely many values and
  known at that stopping time.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_boundedShift` — Itô's formula for the increment of
  a path between two stopping times, for a function translated by a bounded random vector known at
  the earlier time.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_measurableShift` — the same for a function
  translated by a random vector known at the earlier time and subject to no bound.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Weight

variable {Ω : Type u} [MeasurableSpace Ω]

end Weight

section MarkDecomposition

variable {Ω : Type u} {α : Type*}

end MarkDecomposition

section SimpleMark

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*} [MeasurableSpace α]
  [MeasurableSingletonClass α]

end SimpleMark

section TwoPieceMark

variable {Ω : Type u}

end TwoPieceMark

section Approximation

variable {Ω : Type u} [MeasurableSpace Ω]

end Approximation

section MeasurableShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

theorem _root_.LevyStochCalc.Brownian.Ito.itoFormula_between_measurableShift
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ K₂ : ℝ} (hK₁ : ∀ (p : Fin n) (z : Fin n → ℝ), |coordDeriv f' p z| ≤ K₁)
    (hK₂ : ∀ (p q : Fin n) (z : Fin n → ℝ) (ω : Ω) (s : ℝ),
      |coordDeriv₂ f'' p q z| * |∑ k : Fin d, H p k ω s * H q k ω s|
        ≤ K₂ * |∑ k : Fin d, H p k ω s * H q k ω s|)
    {T : ℝ} (hT : 0 < T)
    {c : Ω → Fin n → ℝ} (hc : Measurable[hσ.measurableSpace] c)
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
          ∂volume ∂P < ⊤) :
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
