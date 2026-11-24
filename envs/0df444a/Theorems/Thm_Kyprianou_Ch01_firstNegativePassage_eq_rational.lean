-- Prove2me | Theorems.Thm_Kyprianou_Ch01_firstNegativePassage_eq_rational
-- name    : Kyprianou.Ch01.firstNegativePassage_eq_rational
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T16:58:46.171902+00:00
-- url     : https://prove2.me/theorems/2ae01875-483e-4003-aca7-f1998374054e
-- title:
--   Source first-negative passage equals its rational-grid clock
-- statement:
--   Under joint product measurability of an integer-valued path $X$, identify the source first strict-negative passage
--   $$\tau_0^-(\omega)=\inf\{t>0:X_t(\omega)<0\}\in\overline{\mathbb{R}}_{\ge 0}$$
--   with the countable rational-grid clock $\tau^{\mathbb{Q}}$. This is the critical leaf in the measurability reduction for `firstNegativePassageMeasurable`, parallel to the proved right-continuous identification `firstNonpositiveLatticeEqRationalOfRightContinuous`. Path regularity needed for the identification (if any beyond joint measurability) should be discharged here or by strengthening the hypothesis in line with Kyprianou §1.3.4.
-- source:
--   Kyprianou (2006), Section 1.3.4; analogue of Prove2Me theorem Kyprianou.Ch01.firstNonpositiveLatticeEqRationalOfRightContinuous (63f8b2f6-625b-42e0-9e2a-c94f66721b02).

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.firstNegativePassage_eq_rational
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℤ)
    (hX : Measurable (fun p : Ω × ℝ≥0 => X p.2 p.1))
    (ω : Ω) :
    firstNegativePassage X ω =
      ⨅ r : ℚ,
        if 0 < (r : ℝ) ∧ X (Real.toNNReal (r : ℝ)) ω < 0 then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤ := by
  sorry
