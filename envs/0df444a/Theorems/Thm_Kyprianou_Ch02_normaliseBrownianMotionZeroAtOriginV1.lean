-- Prove2me | Theorems.Thm_Kyprianou_Ch02_normaliseBrownianMotionZeroAtOriginV1
-- name    : Kyprianou.Ch02.normaliseBrownianMotionZeroAtOriginV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T21:37:28.237812+00:00
-- url     : https://prove2.me/theorems/15fac9f6-c802-43a6-aaf4-a80051d87dfd
-- title:
--   Pathwise centred KLS Brownian driver retains Brownian structure
-- statement:
--   Construct a KLS BrownianMotion by subtracting the initial random value B.W 0 pointwise at every time. The increment Gaussian laws are unchanged. Measurability, joint measurability, continuous paths almost surely and negative-time zero almost surely are preserved. Joint past-future independence follows because normalised history is a measurable sub-sigma-algebra of the original Brownian history and the future increments agree exactly. The resulting process has Bprime.W0=0 identically.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.1: normalised independent driving Brownian motion.

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

theorem normaliseBrownianMotionZeroAtOriginV1
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : LevyStochCalc.Brownian.BrownianMotion P) :
    ∃ B' : LevyStochCalc.Brownian.BrownianMotion P,
      ∀ (t : ℝ) (ω : Ω),
        B'.W t ω = B.W t ω - B.W 0 ω := by sorry

end Kyprianou.Ch02
