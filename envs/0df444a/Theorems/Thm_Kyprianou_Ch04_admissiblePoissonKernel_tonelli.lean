-- Prove2me | Theorems.Thm_Kyprianou_Ch04_admissiblePoissonKernel_tonelli
-- name    : Kyprianou.Ch04.admissiblePoissonKernel_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T08:19:29.35714+00:00
-- url     : https://prove2.me/theorems/3be1b411-7c1c-4e67-8dd9-e2eaa5bd543b
-- title:
--   Admissible Poisson kernels admit Tonelli interchange of expectation and jump intensity
-- statement:
--   For a published admissible predictable Poisson kernel phi, its joint measurability allows the nonnegative integration over sample-space probability and the jump-size intensity measure to be interchanged at each fixed time. This gives the deterministic Tonelli step of Chapter 4 Theorem 4.4 without requiring an extra measurability hypothesis. It does not itself establish Poisson compensation of random jump counts.
-- source:
--   Kyprianou (2006) Chapter 4 Theorem 4.4 printed p.95; mathematical helper derived from the Proved ProbabilityTheory Chapter 8 Tonelli theorem thm_8_3. Full source privately compiled at exact pin in job 8b498c0c-12d6-4aef-9c75-16ea31a58839.

import Mathlib
import Theorems.Thm_thm_8_3
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.admissiblePoissonKernel_tonelli
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure ℝ) [SigmaFinite ν]
    (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (phi : ℝ → ℝ → Ω → ℝ)
    (hPhi : Kyprianou.Ch04.IsAdmissiblePoissonKernel P F phi)
    (t : ℝ≥0) :
    (∫⁻ ω, ∫⁻ x, ENNReal.ofReal (phi (t : ℝ) x ω) ∂ν ∂P) =
    (∫⁻ x, ∫⁻ ω, ENNReal.ofReal (phi (t : ℝ) x ω) ∂P ∂ν) := by sorry
