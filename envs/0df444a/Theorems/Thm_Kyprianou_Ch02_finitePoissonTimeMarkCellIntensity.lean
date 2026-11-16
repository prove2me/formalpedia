-- Prove2me | Theorems.Thm_Kyprianou_Ch02_finitePoissonTimeMarkCellIntensity
-- name    : Kyprianou.Ch02.finitePoissonTimeMarkCellIntensity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T21:49:56.692099+00:00
-- url     : https://prove2.me/theorems/893a0c01-32f5-4ca3-a1e2-7cec4ffcc325
-- title:
--   Finite intensity of each bounded time and finite mark cell
-- statement:
--   A measurable finite-intensity mark cell and a bounded unit time interval produce a finite Poisson reference-intensity time-mark cell. Exact source subgoal hA_fin of PoissonRandomMeasure.exists_of_sigmaFinite in LevyStochCalc.
-- source:
--   LevyStochCalc/Poisson/RandomMeasure.lean, exists_of_sigmaFinite, source hA_fin subgoal; Chapter 2 Theorem 2.4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory LevyStochCalc.Poisson
open scoped ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem finitePoissonTimeMarkCellIntensity
    {E : Type} [MeasurableSpace E]
    (ν : Measure E) (s : ℕ → Set E)
    (hs_meas : ∀ m, MeasurableSet (s m))
    (hs_fin : ∀ m, ν (s m) < ⊤) :
    ∀ q : ℕ × ℕ,
      LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ico (q.1 : ℝ) (q.1 + 1) ×ˢ s q.2) ≠ ⊤ := by sorry

end Kyprianou.Ch02
