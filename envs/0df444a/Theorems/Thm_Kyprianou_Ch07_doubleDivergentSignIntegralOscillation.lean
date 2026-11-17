-- Prove2me | Theorems.Thm_Kyprianou_Ch07_doubleDivergentSignIntegralOscillation
-- name    : Kyprianou.Ch07.doubleDivergentSignIntegralOscillation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-16T21:18:07.551842+00:00
-- url     : https://prove2.me/theorems/0bb2eb25-d968-4ba8-81ca-f39ab4525071
-- title:
--   Theorem 7.1(iii): a nontrivial Lévy process with both divergent sign integrals oscillates
-- statement:
--   Derive pathwise upper and lower unboundedness from the exhaustive nontrivial Lévy drift/oscillation trichotomy and divergence of both Spitzer time-sign integrals.
-- source:
--   Kyprianou (2006), Theorem 7.1, printed p. 180; original PDF p. 189, source-faithful source clauses. The nontriviality requirement in part (iii) is retained exactly from the published Chapter 7 target, excluding the zero-process counterexample. Parent target b19f9427-4332-4378-b603-d7bbc9d19db8.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_DriftOscillationObservables
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.doubleDivergentSignIntegralOscillation
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hPlusInfinite : Kyprianou.Ch07.nonnegativeSignIntegral P X = ⊤)
    (hMinusInfinite : Kyprianou.Ch07.nonpositiveSignIntegral P X = ⊤)
    (hNontrivial : Kyprianou.Ch07.IsNontrivialLevyProcess P X) :
    Kyprianou.Ch07.OscillatesAtInfinity P X := by
  sorry
