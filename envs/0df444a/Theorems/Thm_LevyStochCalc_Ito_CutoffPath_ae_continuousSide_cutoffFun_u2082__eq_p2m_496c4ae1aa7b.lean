-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_CutoffPath_ae_continuousSide_cutoffFun_u2082__eq_p2m_496c4ae1aa7b
-- name    : LevyStochCalc.Ito.CutoffPath.ae_continuousSide_cutoffFun_u2082__eq_p2m_496c4ae1aa7b
-- status  : Open
-- author  : @WillR
-- created : 2026-11-21T09:56:35.809445+00:00
-- url     : https://prove2.me/theorems/f1ad6e57-7707-41b2-b168-25b78fb2cf4c
-- title:
--   ae continuousSide cutoffFun₂ eq
-- statement:
--   The source theorem `LevyStochCalc.Ito.CutoffPath.ae_continuousSide_cutoffFun₂_eq` is extracted from `LevyStochCalc.Ito.CutoffPathAgreement`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_CutoffPathAgreement_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Agreement of the continuous integrands with their cut-off, along a confined path

`JumpFormulaCutoff.integrands_cutoffFun₂_eq_of_mem` compares all five integrands of a state
function with those of its cut-off, and for the two jump integrands it needs the jump coefficient
itself bounded over the window, for every mark. That hypothesis is not available in general: the
jump coefficient is only square integrable against the intensity, so `x + γ(s, x, e)` leaves
every ball however large the cut-off radius.

The three *continuous* integrands need no such hypothesis. They are read at path values only, so
a path confined to a ball is enough. `integrands_cutoffFun₂_eq_of_boundedPath` records that,
adding the gradient, which the pathwise form of the jump part also reads at path values.

For the Brownian transfer the confinement has to come from a stopping time rather than an event,
so the same agreement is restated below `min (openExitTime …) T`: strictly below the exit time
the path is in the ball, and strictly below `T` the time cut-off is inactive. That is exactly the
hypothesis shape of `stochasticIntegralBrownian_congr_of_lt`.

## Main statements

* `integrands_cutoffFun₂_eq_of_boundedPath` — drift, diffusion, path value and gradient agree
  with their cut-off along a path confined to the ball, with no hypothesis on the jumps.
* `boundedPathSet_subset_le_openExitTime` — a path confined to the ball over the window has not
  exited by the end of it.
* `diffusionIntegrand_cutoffFun₂_eq_of_lt` — the agreement in the form the strict locality
  transfer consumes.
* `stochasticIntegralBrownian_cutoffFun₂_eq_of_le`, `multidimIntegral_cutoffFun₂_eq_of_mem` —
  the Brownian term of the cut-off and of the function itself agree almost surely on the event
  that the path has not left the ball, componentwise and in the vector form.
* `ae_continuousSide_cutoffFun₂_eq` — the whole continuous side, endpoints and drift integral
  included, agrees on that event.
* `norm_leftLimPathAt_le_of_boundedPath`,
  `gradient_cutoffFun₂_leftLim_eq_of_boundedPath` — a confined path has its left limits in the
  ball, where the gradient of the cut-off is that of the function.
* `cutoffFun₂_leftLim_eq_of_boundedPath`,
  `jumpIncrement_sub_eq_compensatorDrift_sub_of_boundedPath` — the cut-off changes the jump
  increment and the compensator-drift integrand by the same amount at the left limits.
* `jumpIncrement_cutoffFun₂_eq_of_boundedPath`,
  `ae_setIntegral_jumpIncrement_cutoffFun₂_eq`, `ae_setIntegral_jumpIncrement_sub_eq_zero` — the
  jump increment agrees with its cut-off at every atom of a window of finite intensity, because
  the state reached by the jump is a value of the path; hence the two integrals against the
  random measure agree and their difference integrates to zero.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Ito.JumpFormulaCutoff

universe u v

variable {Ω : Type u} {n d : ℕ} {E : Type v}

section BrownianTransfer

open MeasureTheory
open LevyStochCalc.Ito.JumpFormula (diffusionIntegrand)

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {E : Type v}

theorem _root_.LevyStochCalc.Ito.CutoffPath.ae_continuousSide_cutoffFun_u2082__eq_p2m_496c4ae1aa7b
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    {Xp : ℝ → Ω → Fin n → ℝ} {coeffs : Setting.JumpDiffusionCoeffs n d E}
    (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) (hT : 0 < T)
    (hadapt : Adapted ℱ Xp)
    (hright : ∀ (ω : Ω) (s : ℝ),
      Filter.Tendsto (fun r => Xp r ω) (nhdsWithin s (Set.Ioi s)) (nhds (Xp s ω)))
    (hm₁ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s =>
      diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j))
    (hp₁ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s =>
      diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j)
    (hq₁ : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s =>
      diffusionIntegrand u coeffs.σ s (Xp s ω) j))
    (hp₂ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s =>
      diffusionIntegrand u coeffs.σ s (Xp s ω) j)
    (hq₂ : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (Xp s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      (cutoffFun₂ u (2 * (m : ℝ)) T (Xp T ω) - cutoffFun₂ u (2 * (m : ℝ)) 0 (Xp 0 ω)
          - (∫ s in Set.Icc (0 : ℝ) T,
              JumpFormula.driftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs s (Xp s ω))
          - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
              (fun s ω => diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω))
              hm₁ hp₁ hq₁ T ω)
        = u T (Xp T ω) - u 0 (Xp 0 ω)
          - (∫ s in Set.Icc (0 : ℝ) T, JumpFormula.driftIntegrand u coeffs s (Xp s ω))
          - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
              (fun s ω => diffusionIntegrand u coeffs.σ s (Xp s ω)) hm₂ hp₂ hq₂ T ω := by sorry
