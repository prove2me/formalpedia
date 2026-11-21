-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_IsVectorItoVersion_vectorItoFormula_decomp_ae
-- name    : LevyStochCalc.Brownian.Ito.IsVectorItoVersion.vectorItoFormula_decomp_ae
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:43:39.259715+00:00
-- url     : https://prove2.me/theorems/c5e3bcbb-8341-4fe8-b976-f8325e95bf48
-- title:
--   vectorItoFormula decomp ae
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.vectorItoFormula_decomp_ae` is extracted from `LevyStochCalc.Brownian.VectorItoFormulaDecomp`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoFormulaDecomp_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The grid decomposition behind Itô's formula in the vector case

Expanding `f(X_T) − f(X_0)` cell by cell along a uniform grid leaves the second-order Taylor
remainder together with three Riemann sums — one for each of the drift, the stochastic and the
quadratic-variation integrals. In coordinates the first-order term splits over the state index
and the Brownian index, and the second-order term over a pair of state indices.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_apply_fderiv_eq` — the first-order Taylor sum in coordinates.
* `LevyStochCalc.Brownian.Ito.sum_apply_fderiv₂_eq` — the second-order Taylor sum in coordinates.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.vectorItoFormula_decomp_ae` — the defect of
  Itô's formula as the remainder plus the three families of Riemann-sum errors.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Reindex

variable {n d : ℕ}

end Reindex

section TaylorSums

variable {n : ℕ}

end TaylorSums

section Decomposition

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}

theorem _root_.LevyStochCalc.Brownian.Ito.IsVectorItoVersion.vectorItoFormula_decomp_ae
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ}
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)
        - ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
              (hmg p k) (hpg p k) (hqg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume))
      =ᵐ[P] fun ω : Ω =>
        taylorRemainderNormed f f' f'' (fun i => X (unifGrid T m i) ω) m
        + (∑ p : Fin n, ((∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * bdrift p ω s ∂volume))
        + (∑ p : Fin n, ∑ k : Fin d,
            ((∑ i ∈ Finset.range m, coordDeriv f' p (X (unifGrid T m i) ω)
                * (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m (i + 1)) ω
                  - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k (unifGrid T m i) ω))
              - stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
                  (fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
                  (hmg p k) (hpg p k) (hqg p k) T ω))
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            ((∑ i ∈ Finset.range m, coordDeriv₂ f'' p q (X (unifGrid T m i) ω)
                * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
                  * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
              - ∫ s in Set.Ioc (0 : ℝ) T,
                  coordDeriv₂ f'' p q (X s ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) := by sorry
