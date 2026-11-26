-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_record_ae_continuous
-- name    : Kyprianou.Ch04.kw48_record_ae_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:34:13.836302+00:00
-- url     : https://prove2.me/theorems/ec45b8a0-4921-4e59-8589-6a31f74c93bc
-- title:
--   Complex reflected path continuous almost everywhere for the record measure
-- statement:
--   Countable discontinuities of the cadlag process have zero measure for the atomless running-supremum Stieltjes measure, and the running supremum is continuous.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch02_cadlagNNRealDiscontinuitiesCountableV1
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_real_atoms
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The reflected characteristic path is continuous almost everywhere for
the atomless running-record measure on every positive-time interval. -/

theorem Kyprianou.Ch04.kw48_record_ae_continuous {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (alpha beta : Real) (w : Ω)
    (a b : NNReal) :
    ∀ᵐ s ∂((dividendMeasure (runningSup L) w).restrict
      (Ioc (a:Real) (b:Real))),
      ContinuousAt (fun r : Real => Z L alpha beta r.toNNReal w) s := by sorry
