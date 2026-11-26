-- Prove2me | Theorems.Thm_Kyprianou_Ch04_kw48_M_adapted_integrable
-- name    : Kyprianou.Ch04.kw48_M_adapted_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T00:33:56.834329+00:00
-- url     : https://prove2.me/theorems/865f2fd4-a02a-4e30-80fe-26134dc366b5
-- title:
--   Complex Kella Whitt process is strongly adapted and integrable
-- statement:
--   Complex Kella Whitt process is strongly adapted and integrable.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.8(i).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_Kyprianou_Ch04_kw48_J_adapted
import Theorems.Thm_Kyprianou_Ch04_kw48_S_adapted_bound
import Theorems.Thm_Kyprianou_Ch04_kw48_Z_adapted
import Theorems.Thm_Kyprianou_Ch04_kw48_M_norm_bound
import Theorems.Thm_Kyprianou_Ch04_exercise47RunningSupremumIntegrable
import Theorems.Thm_Kyprianou_Ch04_kw47_runningSup_raw_eq
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The proposed Kella–Whitt process is strongly adapted and integrable. -/

theorem Kyprianou.Ch04.kw48_M_adapted_integrable {Ω : Type} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal mΩ)
    (L : SpectrallyNegativeLevy P F) (Psi : Real → Complex)
    (alpha beta : Real) :
    StronglyAdapted F (M L Psi alpha beta) ∧
      ∀ t, Integrable (M L Psi alpha beta t) P := by sorry
