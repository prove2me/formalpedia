-- Prove2me | Theorems.Thm_Kyprianou_Ch02_sourceFaithfulLevyExponentSmallLargeSplitV1
-- name    : Kyprianou.Ch02.sourceFaithfulLevyExponentSmallLargeSplitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:53:12.074667+00:00
-- url     : https://prove2.me/theorems/fa0df861-9f09-4e87-9bc1-cf15afe2dd62
-- title:
--   Theorem 2.1 Lévy–Itô exact compensated-exponent splitting between strictly small and large jumps
-- statement:
--   For every source Lévy triplet of arbitrary drift a, Brownian scale sigma and admissible Lévy measure, split the exact complex Lévy–Khintchine exponent into Gaussian-drift, compensated strictly small-jump integral over (-1,1), and complementary large-jump integral over the full complement, including atoms at -1 and 1 in the large-jump component. Use globally integrable compensated Lévy integrand and integral_add_compl. This is the exact source convention required to multiply the three component characteristic functions in Theorem 2.1.
-- source:
--   Kyprianou 2006 Theorem 2.1, Lévy–Khintchine formula (2.5) with strict small-jump cutoff at 1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem sourceFaithfulLevyExponentSmallLargeSplitV1
    (a : ℝ) (σ : ℝ≥0) (levyMeasure : Measure ℝ)
    (hlevyMeasure : ProbabilityTheory.IsLevyMeasure levyMeasure)
    (ξ : ℝ) :
    Kyprianou.Ch01.levyTripleExponent
      ⟨-a, σ ^ 2, levyMeasure, hlevyMeasure⟩ ξ =
    (Complex.I * (((-a) * ξ : ℝ) : ℂ) -
      (((((σ ^ 2 : ℝ≥0) : ℝ) * ξ ^ 2 / 2 : ℝ)) : ℂ)) +
    (∫ x in Set.Ioo (-1 : ℝ) 1,
      ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) +
    (∫ x in (Set.Ioo (-1 : ℝ) 1)ᶜ,
      ProbabilityTheory.levyCompensatedIntegrand ξ x ∂levyMeasure) := by sorry

end Kyprianou.Ch02
