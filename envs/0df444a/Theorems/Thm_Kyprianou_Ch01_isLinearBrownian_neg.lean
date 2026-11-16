-- Prove2me | Theorems.Thm_Kyprianou_Ch01_isLinearBrownian_neg
-- name    : Kyprianou.Ch01.isLinearBrownian_neg
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T20:37:58.697311+00:00
-- url     : https://prove2.me/theorems/e50c78b3-b293-4015-ba70-87995005329f
-- title:
--   Reflected drifted Brownian motion has the same volatility and opposite drift
-- statement:
--   Negating a real Brownian Lévy process preserves its càdlàg and almost-sure continuous paths and its independent and stationary increments, while changing its Gaussian characteristic exponent from drift γ to −γ at unchanged volatility σ. This exact deterministic transformation of the published IsLinearBrownian definition enables the negative-barrier discounted first passage identity to use the already stated positive-barrier theorem.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.10, reflection of drifted Brownian motion.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.isLinearBrownian_neg
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma : ℝ)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma) :
    Kyprianou.Ch01.IsLinearBrownian P
      (fun t ω => -X t ω) sigma (-gamma) := by sorry
