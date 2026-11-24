-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyAbsPowIntegrableIffLargeV1
-- name    : Kyprianou.Ch02.levyAbsPowIntegrableIffLargeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:20:41.413678+00:00
-- url     : https://prove2.me/theorems/70b8f5e7-5bfe-40e2-ab37-8c47dd4f42c3
-- title:
--   Lévy absolute jump powers: full integrability exactly when the large-jump power is integrable
-- statement:
--   Deterministic Lévy integrability split at absolute mark size one, using the bound by the square on small marks for n at least two, and domination of signed powers by absolute powers.
-- source:
--   Kyprianou (2006), Chapter 2, Exercise 2.6 and worked solution; current corrected V3 parent 2d7732b0-159a-41c5-9727-2eb4777ea9df.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem levyAbsPowIntegrableIffLargeV1
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (n : ℕ) (hn : 2 ≤ n) :
    (Integrable (fun x : ℝ => |x| ^ n) ν ↔
      Integrable (fun x : ℝ => |x| ^ n)
        (ν.restrict {x : ℝ | 1 ≤ |x|})) ∧
    (Integrable (fun x : ℝ => |x| ^ n)
        (ν.restrict {x : ℝ | 1 ≤ |x|}) →
      Integrable (fun x : ℝ => x ^ n) ν) := by sorry

end Kyprianou.Ch02
