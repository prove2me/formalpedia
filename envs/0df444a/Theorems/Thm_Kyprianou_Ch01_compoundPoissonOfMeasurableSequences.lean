-- Prove2me | Theorems.Thm_Kyprianou_Ch01_compoundPoissonOfMeasurableSequences
-- name    : Kyprianou.Ch01.compoundPoissonOfMeasurableSequences
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T23:50:33.786681+00:00
-- url     : https://prove2.me/theorems/40b57648-d39e-430a-a57f-200d5fd672e0
-- title:
--   Compound Poisson of measurable sequences is jointly measurable
-- statement:
--   Let $\tau_n$ and $Y_n$ be measurable real functions on $\Omega$ for every $n$.
--
--   The compound-Poisson path
--   $$(\omega,u)\mapsto\xi_u(\omega)$$
--   built from those sequences is jointly measurable on $\Omega\times[0,\infty)$.
-- source:
--   Kyprianou (2006), Section 1.3.4; the real path is measurable once the driver sequences are.

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.compoundPoissonOfMeasurableSequences
    {Ω : Type*} [MeasurableSpace Ω]
    (τ Y : ℕ → Ω → ℝ)
    (hτ : ∀ n, Measurable (τ n))
    (hY : ∀ n, Measurable (Y n)) :
    Measurable
      (fun p : Ω × ℝ≥0 =>
        ProbabilityTheory.compoundPoisson 0 τ Y (p.2 : ℝ) p.1) := by
  sorry
