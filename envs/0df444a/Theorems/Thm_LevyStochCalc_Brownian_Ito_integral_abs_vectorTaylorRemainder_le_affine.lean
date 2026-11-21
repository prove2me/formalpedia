-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_abs_vectorTaylorRemainder_le_affine
-- name    : LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T19:40:06.605421+00:00
-- url     : https://prove2.me/theorems/7153cc83-3b39-4106-8d8d-bf845dbab3e9
-- title:
--   integral abs vectorTaylorRemainder le affine
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine` is extracted from `LevyStochCalc.Brownian.VectorItoTaylor`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoTaylor_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The Taylor remainder of a vector Itô process along a uniform grid

Expanding a twice-differentiable function of a vector Itô process cell by cell leaves a
second-order Taylor remainder. For a Lipschitz second derivative that remainder is cubic in the
increment, so the third moments of the increments bound it in `L¹`; across a uniform grid of `m`
cells the bound is of order `m^{-1/2}`.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_taylorRemainderNormed` — the remainder along a
  measurable sequence is measurable.
* `LevyStochCalc.Brownian.Ito.sum_integral_sq_norm_vectorItoIncrement_le` — the second moments of
  the increments sum to `O(1)`.
* `LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine` — the `L¹` bound under
  an affine oscillation bound on the second derivative.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section RemainderMeasurable

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

end RemainderMeasurable

section VectorTaylor

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in

theorem _root_.LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le_affine (X₀ : Ω → Fin n → ℝ)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} {A K : ℝ} (hA0 : 0 ≤ A)
    (hK0 : 0 ≤ K) (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf''c : Continuous f'') (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ A + K * ‖z - w‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => taylorRemainderNormed f f' f''
        (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m) P
      ∧ ∫ ω, |taylorRemainderNormed f f' f''
          (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m| ∂P
        ≤ A * ((n : ℝ) * (2 * (B ^ 2 * (T * (T / (m : ℝ)))) + 2 * ((d : ℝ) ^ 2 * (C ^ 2 * T))))
          + K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
            + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
              * (T * Real.sqrt (T / (m : ℝ))))))))) := by sorry
