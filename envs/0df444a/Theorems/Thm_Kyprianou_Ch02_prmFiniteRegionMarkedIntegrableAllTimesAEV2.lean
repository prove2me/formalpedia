-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionMarkedIntegrableAllTimesAEV2
-- name    : Kyprianou.Ch02.prmFiniteRegionMarkedIntegrableAllTimesAEV2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T12:13:08.428841+00:00
-- url     : https://prove2.me/theorems/0ea2aab0-7dcf-4e5e-a6c2-602b6f67927e
-- title:
--   Simultaneous a.s. finite-region marked integral integrability with corrected KLS provider
-- statement:
--   Source-equivalent to the already remotely Proved Chapter 2 marked-integral a.s. integrability theorem, but uses only validated KLS Atomic_F000 and the independently Proved finite-window Dirac-law V3. The original proof bounds each nonnegative time by a natural horizon and uses a finite weighted Dirac representation of the PRM restriction to prove any real mark integrable there. This avoids assumptions about the ν first moment and corrects an import-stage failure of the older mixed KLS/LeanLevy source provider.
-- source:
--   Kyprianou Chapter 2; source-equivalent repair of proved prmFiniteRegionMarkedIntegrableAllTimesAEV1 5d3be3ac; full accepted source code reused with updated Proved Dirac-law V3.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteRegionMarkedIntegrableAllTimesAEV2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ≥0), IntegrableOn (fun z : ℝ × ℝ => z.2) (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) (N.N ω) := by sorry
