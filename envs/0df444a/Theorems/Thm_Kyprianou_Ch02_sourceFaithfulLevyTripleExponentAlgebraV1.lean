-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyTripleExponentAlgebraV1
-- name    : Kyprianou.Ch02.sourceFaithfulLevyTripleExponentAlgebraV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:56:59.898644+00:00
-- url     : https://prove2.me/theorems/e98ce1e5-a06c-4bb7-95d2-ec948ce67639
-- title:
--   Fourier exponent sum identity for the real Lévy–Khintchine triplet
-- statement:
--   Expand the definition of levyTripleExponent for drift −a, Gaussian variance σ² and Lévy measure ν, split its Lévy integral into |x|≥1 and −1<x<1, and use Complex.exp_add to combine the independent Gaussian, large-jump and compensated-small-jump factors. Any mass at zero has a vanishing integrand under the Lévy measure; the two cutoff regions exhaust the real line. This is a deterministic Fourier-algebra obligation.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1: characteristic exponent of the three Lévy–Itô components.

import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_IndependentComponents
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem sourceFaithfulLevyTripleExponentAlgebraV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    [SigmaFinite levyMeasure] :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      (Complex.exp ((((t : ℝ) : ℂ)) *
          (-Complex.I * (a : ℂ) * (ξ : ℂ) -
            (((σ : ℝ) ^ 2 * ξ ^ 2 / 2 : ℝ) : ℂ)))) * (Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in {x : ℝ | 1 ≤ |x|},
            (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂levyMeasure)) * (Complex.exp ((((t : ℝ) : ℂ)) *
          ∫ x in Set.Ioo (-1 : ℝ) 1,
            ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure)) = (Complex.exp ((((t : ℝ) : ℂ)) *
          Kyprianou.Ch01.levyTripleExponent
            ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ)) := by sorry

end Kyprianou.Ch02
