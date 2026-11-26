-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41PrezeroMarkedCountZeroV6
-- name    : Kyprianou.Ch04.exercise41PrezeroMarkedCountZeroV6
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T10:31:13.369313+00:00
-- url     : https://prove2.me/theorems/2afec066-74ef-5465-b463-49de8f30da40
-- title:
--   Null predictable occupation implies an almost surely zero physical negative-jump count
-- statement:
--   Null predictable occupation implies an almost surely zero physical negative-jump count
-- source:
--   Kyprianou (2006), Exercise 4.1(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41PrezeroMarkedCountZeroV6
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (G : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P G) (T : NNReal)
    (E : Set (NNReal × Ω)) (hE : MeasurableSet[G.rightCont.predictable] E)
    (hT : ∀ p ∈ E, p.1 ≤ T)
    (hnull : ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
      Real.toNNReal).prod P) E = 0) :
    let NX : Ω → Measure (NNReal × ℝ) := fun w =>
      ((Measure.count.restrict {u : NNReal | 0 < u ∧ L.X u w -
        Function.leftLim (fun v : NNReal => L.X v w) u ≠ 0}).map
        (fun u => (u,L.X u w - Function.leftLim (fun v : NNReal => L.X v w) u)))
    ∀ᵐ w ∂P, NX w {p | (p.1,w) ∈ E ∧ p.2 < 0} = 0  := by
  sorry
