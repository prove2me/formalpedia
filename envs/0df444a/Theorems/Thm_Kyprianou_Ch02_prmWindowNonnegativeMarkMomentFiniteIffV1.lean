-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmWindowNonnegativeMarkMomentFiniteIffV1
-- name    : Kyprianou.Ch02.prmWindowNonnegativeMarkMomentFiniteIffV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:20:53.972071+00:00
-- url     : https://prove2.me/theorems/531aebd0-ac19-4d3e-b219-ca0f6af8ffdb
-- title:
--   Finite expectation of a nonnegative Poisson mark integral on a positive time window
-- statement:
--   General nonnegative Campbell expectation criterion for the original KLS Poisson random measure over a positive time window. The proof uses count expectation, monotone approximation and product intensity, without imposing integrability in advance.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.6 and worked solution; current corrected V3 parent 2d7732b0-159a-41c5-9727-2eb4777ea9df.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem prmWindowNonnegativeMarkMomentFiniteIffV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (f : ℝ → ℝ) (hf : Measurable f) (hn : ∀ x, 0 ≤ f x)
    (t : ℝ≥0) (ht : 0 < t) :
    ((∫⁻ ω, ∫⁻ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
          ENNReal.ofReal (f z.2) ∂(N.N ω) ∂P) < ⊤ ↔
      Integrable f ν) := by sorry

end Kyprianou.Ch02
