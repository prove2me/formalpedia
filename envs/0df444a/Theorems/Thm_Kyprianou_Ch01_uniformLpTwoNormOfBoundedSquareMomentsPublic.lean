-- Prove2me | Theorems.Thm_Kyprianou_Ch01_uniformLpTwoNormOfBoundedSquareMomentsPublic
-- name    : Kyprianou.Ch01.uniformLpTwoNormOfBoundedSquareMomentsPublic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:27:10.969407+00:00
-- url     : https://prove2.me/theorems/127886cf-1363-42de-b681-a72e87706ee5
-- title:
--   A common real second-moment bound gives a common finite L2 seminorm bound
-- statement:
--   For a sequence of almost-everywhere strongly measurable real random variables on any measure space, assume that each square is integrable and all square integrals are bounded above by the same finite nonnegative real K. Then there exists one nonnegative finite real C that bounds the L2 seminorm of every function in the sequence. The result follows from the L2 seminorm's square-root lintegral definition and the equality between the real integral of a nonnegative integrable function and its extended-real lintegral. No uniform-integrability or convergence assumption is used.
-- source:
--   Elementary measure-theoretic L2 moment identity used to deduce uniform integrability for Kyprianou (2006) Chapter 1 Brownian passage.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.uniformLpTwoNormOfBoundedSquareMomentsPublic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (f : ℕ → Ω → ℝ)
    (hMeas : ∀ n, AEStronglyMeasurable (f n) P)
    (K : ℝ) (hK : 0 ≤ K)
    (hMoment : ∀ n, Integrable (fun ω => f n ω ^ 2) P ∧
      (∫ ω, f n ω ^ 2 ∂P) ≤ K) :
    ∃ C : ℝ≥0, ∀ n, eLpNorm (f n) 2 P ≤ (C : ENNReal) := by sorry
