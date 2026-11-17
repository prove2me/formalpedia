-- Prove2me | Theorems.Thm_Kyprianou_Ch06_eventIndependenceOfAlmostSureEquivalentEvents
-- name    : Kyprianou.Ch06.eventIndependenceOfAlmostSureEquivalentEvents
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:12:22.114199+00:00
-- url     : https://prove2.me/theorems/2e193bf7-40f8-4481-ae99-758e6c7bb53a
-- title:
--   Independence of events survives almost-sure equivalence of both factors
-- statement:
--   If both events in an exact probability factorisation are replaced by almost-surely equivalent events, the factorisation is preserved. Prove using three measure_congr applications to the two marginals and their intersection, with unchanged original probability measure.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.eventIndependenceOfAlmostSureEquivalentEvents
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (D D' G G' : Set Omega)
    (hD : ∀ᵐ omega ∂P, (omega ∈ D) ↔ (omega ∈ D'))
    (hG : ∀ᵐ omega ∂P, (omega ∈ G) ↔ (omega ∈ G'))
    (hInd : P (D' ∩ G') = P D' * P G') :
    P (D ∩ G) = P D * P G := by sorry
