-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Multidim_MultidimBrownianMotion_exists_everywhere_cadlag_vectorIntegral
-- name    : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T22:01:44.460616+00:00
-- url     : https://prove2.me/theorems/596c41cc-0b0b-4fa1-b1ea-c31babfff399
-- title:
--   exists everywhere cadlag vectorIntegral
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral` is extracted from `LevyStochCalc.Brownian.CadlagVectorIntegral`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CadlagVectorIntegral_F000
import Definitions.Def_LevyStochCalc_Probability_ProgressiveCadlag_F001

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# An everywhere-càdlàg version of the multidimensional Brownian integral

The multidimensional `L²` Itô integral `∫_0^t Z_s · dW_s = ∑_i ∫_0^t Z_s^i dW_s^i` is defined
separately at each time, so it carries no path regularity. Each coordinate integral has an
adapted modification with almost surely càdlàg paths; when the null set on which the paths fail
to be càdlàg belongs to `ℱ 0` and the filtration is constant before time `0`, that modification
can be replaced by `0` there, which makes every path càdlàg. Summing the `d` coordinate
modifications gives a version of the vector integral that is adapted to the right-continuous
filtration, jointly measurable, càdlàg at every sample point and a martingale.

## Main statements

* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.martingale_finsetSum` — a finite sum
  of martingales is a martingale.
* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral`
  — the multidimensional Brownian integral has an everywhere-càdlàg martingale version.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim
namespace MultidimBrownianMotion

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {d : ℕ}

theorem _root_.LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral
    (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ i : Fin d, IsBrownianFiltration (W.W i) ℱ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (hm : ∀ i : Fin d, Measurable (Function.uncurry (fun ω s => Z s ω i)))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ (fun ω s => Z s ω i))
    (hq : ∀ i : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    ∃ M : ℝ → Ω → ℝ, Adapted ℱ.rightCont M ∧ Measurable (Function.uncurry M) ∧
      (∀ t : ℝ, M t =ᵐ[P] fun ω =>
        MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z hm hp hq t ω) ∧
      (∀ (ω : Ω) (t : ℝ),
        Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)) ∧
          ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)) ∧
      Martingale M ℱ.rightCont P := by sorry
