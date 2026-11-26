-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_record_phase_change
-- name    : Kyprianou.Ch04.kw48_record_phase_change
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:51:34.948369+00:00
-- url     : https://prove2.me/theorems/cc32a0f3-3f7f-4723-a262-cbbbff15cd64
-- title:
--   Continuous running-record Stieltjes change of variable
-- statement:
--   The continuous running-record phase integral over a time interval equals the difference of its level-coordinate primitives, by uniqueness of limits of the two quadratures.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_record_measure_grid_limit
import Theorems.Thm_Kyprianou_Ch04_kw48_record_phase_level_grid
import Theorems.Thm_Kyprianou_Ch04_kw47_capped_uniform_grid
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Change variables in the continuous monotone record integral by
comparing the time and record-level quadratures of the same phase. -/

theorem Kyprianou.Ch04.kw48_record_phase_change {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F) (beta : Real) (w : Ω)
    (a b : NNReal) (hab : a ≤ b) :
    (∫ s in Ioc (a:Real) (b:Real),
      Complex.exp (Complex.I*(beta:Complex)*(runningSup L s.toNNReal w:Complex))
      ∂(dividendMeasure (runningSup L) w)) =
      S L beta b w - S L beta a w := by sorry
