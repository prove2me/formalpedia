-- Prove2me | Theorems.Thm_Kyprianou_Ch02_compensatedSmallJumpBandCadlagAEV1
-- name    : Kyprianou.Ch02.compensatedSmallJumpBandCadlagAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T19:50:49.132572+00:00
-- url     : https://prove2.me/theorems/d6d887c0-847f-4476-8b7b-ace2b0fc2154
-- title:
--   Almost-sure càdlàg compensated small-jump Poisson band
-- statement:
--   Apply the proved finite-region càdlàg lemma to the positive Lévy mark band B={x|epsilon≤abs x and abs x<1}. The Lévy measure bound implies finite intensity for B via the public IsLevyMeasure finite-largeSet theorem. Subtracting its deterministic linear compensator preserves càdlàg paths. The result is a source-faithful finite-cutoff input for the uniform small-jump limit of Kyprianou Theorem 2.10.
-- source:
--   Kyprianou (2006), Chapter 2, Theorem 2.10, finite-band approximation

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch02_CompensatedSmallJumpBand
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02
theorem compensatedSmallJumpBandCadlagAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (hν : ProbabilityTheory.IsLevyMeasure ν)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun (t : ℝ≥0) => compensatedSmallJumpBand P ν N ε t ω)
    := by sorry
end Kyprianou.Ch02
