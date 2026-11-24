-- Prove2me | Theorems.Thm_Kyprianou_Ch03_strongMarkovCommonCoordinateLimitMeasV1
-- name    : Kyprianou.Ch03.strongMarkovCommonCoordinateLimitMeasV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T07:46:46.091789+00:00
-- url     : https://prove2.me/theorems/c7e001f8-3e5f-44aa-8b80-40f007ad48cd
-- title:
--   Common-event path measurability
-- statement:
--   Patch the limit and every approximant to zero on one measurable null superset of the failure of simultaneous convergence, then apply measurable scalar pointwise limits.
-- source:
--   Kyprianou (2006), Theorem 3.1; parent 6ca4e517-a112-432a-b338-6d002fb7c8aa.

import Mathlib
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch03.strongMarkovCommonCoordinateLimitMeasV1
    {Omega : Type} [MeasurableSpace Omega]
    (mu : Measure Omega)
    (Y : ℕ → Omega → (NNReal → Real)) (Z : Omega → (NNReal → Real))
    (hMeas : ∀ n, Measurable (Y n))
    (hLimit : ∀ᵐ w ∂mu, ∀ u : NNReal,
      Tendsto (fun n => Y n w u) atTop (nhds (Z w u))) :
    AEMeasurable Z mu := by
  sorry
