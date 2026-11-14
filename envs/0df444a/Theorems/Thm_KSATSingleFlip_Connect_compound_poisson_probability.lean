-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_compound_poisson_probability
-- name    : KSATSingleFlip.Connect.compound_poisson_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:23:24.840726+00:00
-- url     : https://prove2.me/theorems/1edb7a63-02a7-43e2-843b-310c383f715a
-- title:
--   Compound Poisson law has unit mass
-- statement:
--   For any finite intensity measure μ on the real line, the compound Poisson measure used in the soft-field recursion has total mass one. This establishes the normalization needed for the mass recursion in Lemma 4.5.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Definition 4.2 and proof of Lemma 4.5, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Mathlib
set_option autoImplicit false
open MeasureTheory ProbabilityTheory KSATSingleFlip.Connect
open scoped ENNReal NNReal

theorem KSATSingleFlip.Connect.compound_poisson_probability (μ : Measure ℝ) [IsFiniteMeasure μ] : compoundPoisson μ Set.univ = 1 := by sorry
