-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_itoFormula_between_gridShift
-- name    : LevyStochCalc.Brownian.Ito.itoFormula_between_gridShift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T08:18:46.083778+00:00
-- url     : https://prove2.me/theorems/3885de1d-c720-492e-a7f8-158f7c38e901
-- title:
--   itoFormula between gridShift
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.itoFormula_between_gridShift` is extracted from `LevyStochCalc.Ito.ItoFormulaGridShift`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaGridShift_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula between two stopping times of unrestricted range

A stopping time is approximated from above by the stopping time that stops at the first point of
a uniform grid strictly beyond it, which takes finitely many values below the horizon. Itô's
formula for the increment of a path between two such discretisations, for a `C²` function
translated by a random vector, passes to the limit: the boundary term converges by continuity of
the function and of the path, the two Lebesgue terms converge along almost every path by
domination, and the stochastic term converges in `L²` because the energy of the difference of two
increments is at most twice the sum of the two energies, hence almost surely along a subsequence
common to the finitely many Brownian channels.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurableSpace_le_gridStop` — the σ-algebra of a stopping time is
  contained in that of its upward grid discretisation.
* `LevyStochCalc.Brownian.Ito.tendsto_stopped_gridStop` — the integrand cut off at the grid
  discretisations converges pointwise at every positive time of the window.
* `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_gridStop` — the Lebesgue terms
  converge along the path.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_sub_gridStop` — the increments cut off at the
  grid discretisations converge in the energy of the window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridShift` — Itô's formula for the increment of a
  path between two stopping times of unrestricted range.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section GridMeasurableSpace

variable {Ω : Type u} [MeasurableSpace Ω]

end GridMeasurableSpace

section PointwiseLimit

variable {Ω : Type u}

end PointwiseLimit

section LebesgueTerm

variable {Ω : Type u} [MeasurableSpace Ω]

end LebesgueTerm

section EnergyTerm

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end EnergyTerm

section GridShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

theorem _root_.LevyStochCalc.Brownian.Ito.itoFormula_between_gridShift
    {X : ℝ → Ω → Fin n → ℝ} (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (hXc : ∀ ω, Continuous fun s : ℝ => X s ω)
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {bdrift : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
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
    {c : Ω → Fin n → ℝ} (hc : Measurable c)
    (hbint : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (fun s => bdrift p ω s) (Set.Ioc (0 : ℝ) T) volume)
    (hQint : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Ioc (0 : ℝ) T) volume)
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
    (hmSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStop τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStop σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped (gridStop τ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
          - Probability.stopped (gridStop σ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped (gridStop σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hbase : ∀ m : ℕ,
      (fun ω : Ω => f (X (clipTime (gridStop τ T m) T ω) ω + c ω)
          - f (X (clipTime (gridStop σ T m) T ω) ω + c ω))
        =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (gridStop τ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
              - Probability.stopped (gridStop σ T m)
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped (gridStop τ T m)
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                    - Probability.stopped (gridStop σ T m)
                        (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
                (hmSm m p k) (hpSm m p k) (hqSm m p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped (gridStop τ T m)
                  (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped (gridStop σ T m)
                    (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
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
