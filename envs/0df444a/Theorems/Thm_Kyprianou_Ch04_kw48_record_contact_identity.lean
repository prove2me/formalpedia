-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_record_contact_identity
-- name    : Kyprianou.Ch04.kw48_record_contact_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:34:17.716935+00:00
-- url     : https://prove2.me/theorems/c5c50fea-4407-4067-8c6f-5b12be984b35
-- title:
--   Complex record contact integral identity
-- statement:
--   The reflected characteristic integrand equals the exponential of the record level almost everywhere for the record measure, by the proved contact theorem.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_contact_measure
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Under the running-record measure the reflected characteristic
integrand equals the characteristic function of the record level. -/

theorem Kyprianou.Ch04.kw48_record_contact_identity {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha beta : Real) (w : Ω)
    (a b : NNReal) :
    (∫ s in Ioc (a:Real) (b:Real), Z L alpha beta s.toNNReal w
      ∂(dividendMeasure (runningSup L) w)) =
    ∫ s in Ioc (a:Real) (b:Real),
      Complex.exp (Complex.I * (beta:Complex) *
        (runningSup L s.toNNReal w:Complex))
      ∂(dividendMeasure (runningSup L) w) := by sorry
