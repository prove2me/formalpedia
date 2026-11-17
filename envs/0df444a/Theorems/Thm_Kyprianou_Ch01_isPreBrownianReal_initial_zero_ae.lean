-- Prove2me | Theorems.Thm_Kyprianou_Ch01_isPreBrownianReal_initial_zero_ae
-- name    : Kyprianou.Ch01.isPreBrownianReal_initial_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:16:11.03884+00:00
-- url     : https://prove2.me/theorems/03d425e5-8224-479e-8acd-bbb80af29969
-- title:
--   A Brownian pre-process starts at zero almost surely from its zero-variance Gaussian marginal
-- statement:
--   Every Mathlib Brownian pre-process on a probability measure space has value zero almost surely at time zero. This follows directly from its Gaussian law at time zero, the pinned Mathlib equality that a zero-variance Gaussian distribution is Dirac at its mean, and the HasLaw.ae_eq_of_dirac theorem. This establishes the source-normalisation premise required to replace almost-sure Brownian start zero by a pathwise zero-start process when proving the genuine Lévy process existence part of Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Pinned Mathlib IsPreBrownianReal.hasLaw_eval, gaussianReal_zero_var, HasLaw.ae_eq_of_dirac; Kyprianou (2006) Chapter 1 Theorem 1.6.

import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.isPreBrownianReal_initial_zero_ae
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal X P) :
    ∀ᵐ ω ∂P, X 0 ω = 0 := by
  sorry
