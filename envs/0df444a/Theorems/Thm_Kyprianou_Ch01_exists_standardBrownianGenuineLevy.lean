-- Prove2me | Theorems.Thm_Kyprianou_Ch01_exists_standardBrownianGenuineLevy
-- name    : Kyprianou.Ch01.exists_standardBrownianGenuineLevy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:24:37.633841+00:00
-- url     : https://prove2.me/theorems/f5bb140c-97ee-49bf-bc48-1e25d8012c7f
-- title:
--   Existence of a standard Brownian Lévy process on a genuine probability space
-- statement:
--   There exists a measurable sample space and a probability measure carrying a real-valued process indexed by nonnegative time that satisfies every condition of the genuine LeanLevy IsLevyProcess predicate. A witness is the pinned Mathlib canonical Brownian path-space law GaussianLimit, and its canonical Brownian coordinate process with the actual initial coordinate subtracted pathwise. The already-Proved Brownian identification and the explicit source-faithful Brownian-to-Lévy conversion provide the full theorem. This is the key Gaussian component needed for Kyprianou Chapter 1 Theorem 1.6.
-- source:
--   Proved ProbabilityTheory.isBrownianReal_brownian_avram UUID 50615216-6ce4-4ba6-b636-9c3624258524; GaussianLimit BrownianMotion source; Kyprianou Chapter 1 Theorem 1.6.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_KLSModular_BrownianMotion_Gaussian_BrownianMotion
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.exists_standardBrownianGenuineLevy :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess X P := by
  sorry
