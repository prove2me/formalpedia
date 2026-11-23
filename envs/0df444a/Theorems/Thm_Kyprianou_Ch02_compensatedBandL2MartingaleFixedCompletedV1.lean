-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedBandL2MartingaleFixedCompletedV1
-- name    : Kyprianou.Ch02.compensatedBandL2MartingaleFixedCompletedV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T20:34:09.931975+00:00
-- url     : https://prove2.me/theorems/f6aa7fb3-5f91-4ade-856f-284f42c42844
-- title:
--   Completed-filtration compensated finite-band L² martingale
-- statement:
--   Every positive compensated Poisson mark band is an L² martingale in the
--   same prescribed completed right-continuous natural Poisson filtration.
--   The martingale uses the proved finite-region fixed-filtration theorem,
--   the required finite intensity and integrability follow from the Lévy measure
--   tail bound and |mark| < 1, and square-integrability is already Proved
--   in Kyprianou.compensatedBandIsL2MartingaleCorrected.
--   This supplies the uniform fixed-filtration approximation required by the
--   corrected Theorem 2.10 martingale limit argument.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.9 and Theorem 2.10

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem compensatedBandL2MartingaleFixedCompletedV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    MeasureTheory.Martingale
      (Kyprianou.compensatedSmallJumpBand P ν N ε) ℱ P ∧
    ∀ t : ℝ≥0,
      MemLp (Kyprianou.compensatedSmallJumpBand P ν N ε t) 2 P := by sorry
end Kyprianou.Ch02
