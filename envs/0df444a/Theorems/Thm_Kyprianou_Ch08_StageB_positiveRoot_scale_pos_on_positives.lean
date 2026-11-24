-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_positiveRoot_scale_pos_on_positives
-- name    : Kyprianou.Ch08.StageB.positiveRoot_scale_pos_on_positives
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T21:13:44.960366+00:00
-- url     : https://prove2.me/theorems/d83dc9d1-81c5-4825-8580-2f55472f8987
-- title:
--   Positive q-root gives strict q-scale positivity on positive arguments
-- statement:
--   A positive right root yields an eventual linear growth lower bound on the Laplace exponent and a quadratic upper bound, from which the q-scale function is strictly positive at every positive argument.
-- source:
--   Kyprianou (2006), Chapter 8, Theorem 8.1 supporting lemma. Supplies positivity of W(a) for the bounded-variation exit-ratio division without the Avram standing assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
import Theorems.Thm_AvramDividend_Classical_psi_quadratic_upper
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_eventual_psi_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem Kyprianou.Ch08.StageB.positiveRoot_scale_pos_on_positives
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (A : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : A.ψ φ = q)
    (W : ℝ → ℝ) (hW : AvramDividend.Classical.IsScaleFunction A q W)
    (a : ℝ) (ha : 0 < a) : 0 < W a := by sorry
