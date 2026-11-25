-- Prove2me | Theorems.Thm_Kyprianou_Ch04_independentExpClockEndpointSupJointLaw
-- name    : Kyprianou.Ch04.independentExpClockEndpointSupJointLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:40:28.238643+00:00
-- url     : https://prove2.me/theorems/fea04ffe-04ca-4373-84e1-2a4addea9e7f
-- title:
--   Independent exponential clock transfers the joint signed drawdown and running-supremum law
-- statement:
--   An independent exponential clock and the original process have the same joint signed drawdown and supremum law as the product-clock construction. Use the measurable Pi-path law, countable dyadic endpoint and running maximum approximations, right continuity, and the exponential marginal law. This statement transfers the law without assuming independence of variable-time evaluation.
-- source:
--   Kyprianou (2006), Exercise 4.8(ii–iii), p. 109; Avram product-clock independence 393755b5-3a71-49ba-9bce-b4dda9c9e843.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.independentExpClockEndpointSupJointLaw
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
    let S : Ω → ℝ := fun ω =>
      sSup ((fun s : NNReal => L.X s ω) '' Set.Iic (e ω))
    let D : Ω → ℝ := fun ω => L.X (e ω) ω - S ω
    let Sp : Ω × ℝ → ℝ := fun z => runningSup L z.2.toNNReal z.1
    let Dp : Ω × ℝ → ℝ := fun z =>
      L.X z.2.toNNReal z.1 - Sp z
    Measurable D ∧ Measurable S ∧
      Measure.map (fun ω => (D ω, S ω)) P =
        Measure.map (fun z => (Dp z, Sp z)) (P.prod (expMeasure q)) := by
  sorry
