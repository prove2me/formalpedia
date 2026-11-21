-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_itoFormula_chain
-- name    : LevyStochCalc.Brownian.Ito.itoFormula_chain
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T23:44:29.739788+00:00
-- url     : https://prove2.me/theorems/b8386e8f-b475-4e3b-8a1b-ec63192f6c79
-- title:
--   itoFormula chain
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.itoFormula_chain` is extracted from `LevyStochCalc.Ito.JumpFormulaAssembly`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaAssembly_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula along a chain of stopping times

A path that evolves continuously between the members of a chain of times and is translated by a
vector held fixed on each of the intervals they cut out satisfies, after composition with a
function of the state, a telescoping identity: the increment over the whole window is the sum of
the increments with the translation frozen on each interval plus the sum of the increments of the
translation at the right endpoints. Where the translated path agrees with a second path, the
integrands of the per-interval Itô formulas coincide with the integrands built from that second
path, so the per-interval Lebesgue and Itô integrals collapse into single integrals over the
window.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_range_shift_telescope` — the pathwise telescoping identity.
* `LevyStochCalc.Brownian.Ito.stopped_sub_congr` — the increment of a cut-off integrand between
  two times depends on the integrand only between them.
* `LevyStochCalc.Brownian.Ito.stopped_sub_shift_funext` — the increment of the cut-off integrand
  of a translated path is the increment of the cut-off integrand of the path it agrees with.
* `LevyStochCalc.Brownian.Ito.sum_range_integral_stopped_sub_of_chain` — the Lebesgue integrals
  of the increments along a chain covering `(0, T]` sum to the integral over that window.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sum_range_stopped_sub_of_chain` — the
  Itô integrals of those increments sum to the Itô integral over that window.
* `LevyStochCalc.Brownian.Ito.itoFormula_chain` — Itô's formula over the window for a path
  translated piecewise along a chain, with the per-interval increments as a hypothesis.
* `LevyStochCalc.Brownian.Ito.itoFormula_chain_path` — the same with the two endpoints
  identified with the values of the path the translations agree with.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal

universe u

section Pathwise

variable {Ω : Type*}

end Pathwise

section Support

variable {Ω : Type*}

end Support

section Collapse

variable {Ω : Type*}

end Collapse

section ItoCollapse

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

end ItoCollapse

section Algebra

end Algebra

section Assembly

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ j : Fin d, IsBrownianFiltration (W.W j) ℱ')

include hcoord in

theorem _root_.LevyStochCalc.Brownian.Ito.itoFormula_chain
    {H : Fin n → Fin d → Ω → ℝ → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
    {V X : ℝ → Ω → Fin n → ℝ} {c : ℕ → Ω → Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    {σ : ℕ → Ω → WithTop ℝ} (hσ : ∀ k, MeasureTheory.IsStoppingTime ℱ' (σ k))
    (hmono : ∀ (k : ℕ) (ω : Ω), σ k ω ≤ σ (k + 1) ω)
    (hmG : ∀ (p : Fin n) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p j ω s))
    (hpG : ∀ (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
    (hqG : ∀ (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmD : ∀ p : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s))
    (hqD : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmQ : ∀ p q : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s))
    (hmV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (σ (k + 1))
          (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
        - Probability.stopped (σ k)
            (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s))
    (hpV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped (σ (k + 1))
          (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
        - Probability.stopped (σ k)
            (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s)
    (hqV : ∀ (k : ℕ) (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖Probability.stopped (σ (k + 1))
              (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
            - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hQint : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s)
      (Set.Ioc (0 : ℝ) T) volume)
    {m : ℕ} (h0 : ∀ ω, σ 0 ω = ((0 : ℝ) : WithTop ℝ))
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V s ω + c k ω = X s ω)
    (hcont : ∀ k < m, (fun ω : Ω => f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)
          - f (V (clipTime (σ k) T ω) ω + c k ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (σ (k + 1))
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s
              - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
              (fun ω s => Probability.stopped (σ (k + 1))
                  (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
                - Probability.stopped (σ k)
                    (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s)
              (hmV k p j)
              (hpV k p j)
              (hqV k p j) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped (σ (k + 1)) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
                  * ∑ j : Fin d, H p j ω s * H q j ω s) ω s
                - Probability.stopped (σ k) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
                    * ∑ j : Fin d, H p j ω s * H q j ω s) ω s) ∂volume) :
    ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) ≤ σ m ω →
      f (V T ω + c m ω) - f (V 0 ω + c 0 ω) =
      ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
              (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
              (hmG p j) (hpG p j) (hqG p j) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * (∑ j : Fin d, H p j ω s * H q j ω s) ∂volume)
        + ∑ k ∈ Finset.range m, (f (V (clipTime (σ (k + 1)) T ω) ω + c (k + 1) ω)
            - f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)) := by sorry
