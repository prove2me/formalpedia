-- Prove2me | Theorems.Thm_Kyprianou_Ch05_smithRenewalRatioTransfer
-- name    : Kyprianou.Ch05.smithRenewalRatioTransfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:05:40.216512+00:00
-- url     : https://prove2.me/theorems/8278d6b2-d0ae-4c83-a1d3-4a3826b1364c
-- title:
--   Smith elementary renewal bridge: real ratio with initial renewal
-- statement:
--   A finite positive extended-real renewal-rate limit is unchanged by including the initial renewal and taking the real-valued ratio.
-- source:
--   Kyprianou (2006), Theorem 5.1(iii); exact transfer from SmithRenewal.Elementary.elementary_renewal_theorem b689ea1a-fac8-4240-8c12-fa8e3e439bae to parent 0e4a1289-230f-405a-bb6b-dc73f33160d0.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_SmithRenewal_Elementary_RenewalProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
open Kyprianou.Ch05 SmithRenewal.Elementary

theorem Kyprianou.Ch05.smithRenewalRatioTransfer
    (V H : Real → ENNReal) (m : Real) (hm : 0 < m)
    (hV : ∀ t : Real, 0 ≤ t → V t = 1 + H t)
    (hH : Tendsto (fun t : Real => H t / ENNReal.ofReal t)
      atTop (nhds (ENNReal.ofReal m)⁻¹)) :
    Tendsto (fun t : Real => (V t).toReal / t) atTop (nhds (1 / m)) := by sorry
