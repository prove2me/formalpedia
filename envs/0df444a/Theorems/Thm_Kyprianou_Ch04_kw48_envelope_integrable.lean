-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_envelope_integrable
-- name    : Kyprianou.Ch04.kw48_envelope_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:40:32.708909+00:00
-- url     : https://prove2.me/theorems/a01acf46-67ef-4520-8871-3bbbe88cf68a
-- title:
--   Integrability of the common complex grid envelope
-- statement:
--   Integrability of the common complex grid envelope.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_exercise47RunningSupremumIntegrable
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The common grid envelope is integrable on each deterministic horizon. -/

theorem Kyprianou.Ch04.kw48_envelope_integrable {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) (T : NNReal) :
    Integrable (envelope L Psi alpha beta T) P := by sorry
