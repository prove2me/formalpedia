-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_exists_stochasticIntegralBrownian_finsetSum
-- name    : LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T18:50:03.336105+00:00
-- url     : https://prove2.me/theorems/8bd96887-1c28-4ec2-ace0-32ab40f7801b
-- title:
--   exists stochasticIntegralBrownian finsetSum
-- statement:
--   The source theorem `LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum` is extracted from `LevyStochCalc.Brownian.ItoFinsetSum`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoAlgebraAssociativity_F002
import Definitions.Def_LevyStochCalc_Brownian_ItoLinear_F001
import Definitions.Def_LevyStochCalc_Brownian_ItoZero_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Linearity of the Itô integral over finite sums

Additivity and scaling give the negation, the difference and the sum over a finite index set.
The finite sum is stated existentially in the admissibility data of the summed integrand, which
the induction produces along with the identity.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_neg`
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub`
* `LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum`
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum {ι : Type*}
    (H : ι → Ω → ℝ → ℝ) (hm : ∀ i, Measurable (Function.uncurry (H i)))
    (hp : ∀ i, Probability.ProgressivelyMeasurable ℱ (H i))
    (hq : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (J : Finset ι) {T : ℝ} (hT : 0 < T) :
    ∃ (hms : Measurable (Function.uncurry fun ω u => ∑ i ∈ J, H i ω u))
      (hps : Probability.ProgressivelyMeasurable ℱ fun ω u => ∑ i ∈ J, H i ω u)
      (hqs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
        (‖∑ i ∈ J, H i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      stochasticIntegralBrownian W ℱ hℱ (fun ω u => ∑ i ∈ J, H i ω u) hms hps hqs T
        =ᵐ[P] fun ω => ∑ i ∈ J,
          stochasticIntegralBrownian W ℱ hℱ (H i) (hm i) (hp i) (hq i) T ω := by sorry
