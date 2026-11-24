-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNegativePassageMeasurable
-- name    : Kyprianou.Ch01.firstNegativePassageMeasurable
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T14:19:46.784418+00:00
-- url     : https://prove2.me/theorems/d9fd0249-5cd4-4580-b54e-1b6330078cb3
-- title:
--   First negative passage is measurable
-- statement:
--   Let $X$ be an integer-valued path that is jointly measurable in calendar time and the sample point. Then the first strict negative passage time $\tau_0^-(\omega)\in\overline{\mathbb{R}}_{\ge 0}$ is a measurable function of the sample point $\omega$.
-- source:
--   Kyprianou (2006), Section 1.3.4; measurability of first passage for a jointly measurable walk.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNegativePassageMeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1)) :
    Measurable (fun ω : Ω => firstNegativePassage X ω) := by
  sorry
