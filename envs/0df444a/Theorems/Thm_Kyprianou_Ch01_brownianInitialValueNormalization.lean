-- Prove2me | Theorems.Thm_Kyprianou_Ch01_brownianInitialValueNormalization
-- name    : Kyprianou.Ch01.brownianInitialValueNormalization
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:14:29.806919+00:00
-- url     : https://prove2.me/theorems/72aef530-1b6a-46dd-a801-4eef4c74b473
-- title:
--   Brownian pre-process invariant under subtracting the almost-surely zero initial value
-- statement:
--   For any Brownian pre-process whose value at time zero is almost surely zero, subtracting its actual value at time zero from every trajectory produces a process which starts at zero for every sample path and retains the full pre-Brownian law. Mathlib IsPreBrownianReal.congr transports this law along marginal almost-everywhere equality. The lemma resolves the distinction between almost-sure and strict pathwise starting conditions in the LeanLevy Lévy-process definition, as needed in Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Mathlib pinned 0df444a360eaa60ab8c11dca51a86af692955474, IsPreBrownianReal.congr, Kyprianou (2006), Chapter 1 Lévy process start-zero condition.

import Mathlib.Probability.BrownianMotion.Basic
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.brownianInitialValueNormalization
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal X P)
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0) :
    IsPreBrownianReal (fun t ω => X t ω - X 0 ω) P := by
  sorry
