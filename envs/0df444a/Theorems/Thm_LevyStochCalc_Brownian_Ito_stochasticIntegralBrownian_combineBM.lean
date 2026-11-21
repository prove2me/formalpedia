-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_stochasticIntegralBrownian_combineBM
-- name    : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_combineBM
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:15:32.596686+00:00
-- url     : https://prove2.me/theorems/e3d0afd6-a5d4-4216-b5c4-1915febd026a
-- title:
--   stochasticIntegralBrownian combineBM
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_combineBM` is extracted from `LevyStochCalc.Brownian.ItoDriverLinear`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoL2CompletionMaster_F002
import Definitions.Def_LevyStochCalc_Brownian_LinearCombination_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the Itô integral in the driver

The elementary integral of a simple integrand against a linear combination of Brownian motions is
the corresponding combination of the elementary integrals, and both sides of the resulting
identity are `L²`-limits along the same approximating sequence, so the identity passes to the
`L²` Itô integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

theorem _root_.LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_combineBM (W : Multidim.MultidimBrownianMotion P d)
    {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱB : IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ hℱB H hm hp hq t
      =ᵐ[P] fun ω => ∑ i, c i
        * stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω := by sorry
