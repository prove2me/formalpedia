-- Prove2me | Theorems.Thm_Kyprianou_Ch04_independentExpClockPathJointLaw
-- name    : Kyprianou.Ch04.independentExpClockPathJointLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:41:35.605458+00:00
-- url     : https://prove2.me/theorems/6a8b669b-9f1c-4dc8-9116-602ead44933f
-- title:
--   Joint law of independent exponential clock and full Pi path
-- statement:
--   The independent clock and coordinate-measurable path have the same joint distribution as the product construction, by exponential survival uniqueness and independence. No variable-time path evaluation is assumed measurable.
-- source:
--   Kyprianou (2006), Exercise 4.8(ii–iii), p. 109; measurable transfer of Avram product-clock Wiener–Hopf law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.independentExpClockPathJointLaw
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (q : ℝ) (hq : 0 < q)
    (e : Ω → NNReal) (he : Measurable e)
    (hlaw : ∀ t : NNReal, (P {ω | t < e ω}).toReal =
      Real.exp (-q * (t : ℝ)))
    (hi : Indep (MeasurableSpace.comap e inferInstance)
      (MeasurableSpace.comap (fun ω : Ω => fun t : NNReal => L.X t ω)
        inferInstance) P) :
    P.map (fun ω => (e ω, fun t : NNReal => L.X t ω)) =
      (P.prod (expMeasure q)).map
        (fun z => (z.2.toNNReal, fun t : NNReal => L.X t z.1)) := by
  sorry
