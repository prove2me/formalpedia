-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvUniformSetIntegralLimitV1
-- name    : Kyprianou.Ch04.bvUniformSetIntegralLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:31:29.196596+00:00
-- url     : https://prove2.me/theorems/15d12bb9-4bb7-4256-99b4-874785cf6b96
-- title:
--   Convergence of integrals under uniform convergence on a finite-measure set
-- statement:
--   The uniform limit is integrable. Bound the norm of the difference integral by the uniform error times the finite measure of the set. No countability restriction on the original filter is required.
-- source:
--   Kyprianou (2006), Theorem 4.2, pp. 91–93; compact deterministic estimates.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.bvUniformSetIntegralLimitV1
    {I A : Type} [MeasurableSpace A] (L : Filter I) [L.NeBot]
    (μ : Measure A) (s : Set A) (hs : MeasurableSet s) (hμ : μ s < ⊤)
    (F : I → A → ℝ) (g : A → ℝ)
    (hF : ∀ i, IntegrableOn (F i) s μ)
    (hU : TendstoUniformlyOn F g L s) :
    Tendsto (fun i => ∫ x in s, F i x ∂μ) L (nhds (∫ x in s, g x ∂μ)) := by
  sorry
