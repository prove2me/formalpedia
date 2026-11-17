-- Prove2me | Theorems.Thm_Kyprianou_Ch07_signIntegralNegativeDrift
-- name    : Kyprianou.Ch07.signIntegralNegativeDrift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:18:06.930203+00:00
-- url     : https://prove2.me/theorems/d896eccc-93f4-4070-bc2c-69048a6d4721
-- title:
--   Theorem 7.1(i): finite nonnegative sign integral forces drift to negative infinity
-- statement:
--   Spitzer/Wiener-Hopf time-sign criterion for almost-sure negative drift.
-- source:
--   Kyprianou (2006), Theorem 7.1, printed p. 180; original PDF p. 189, source-faithful source clauses. The nontriviality requirement in part (iii) is retained exactly from the published Chapter 7 target, excluding the zero-process counterexample. Parent target b19f9427-4332-4378-b603-d7bbc9d19db8.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.signIntegralNegativeDrift
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hFinite : Kyprianou.Ch07.nonnegativeSignIntegral P X < ⊤) :
    Kyprianou.Ch07.DriftsToNegInfinity P X := by
  sorry
