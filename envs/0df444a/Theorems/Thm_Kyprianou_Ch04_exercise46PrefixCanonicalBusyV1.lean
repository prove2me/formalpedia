-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46PrefixCanonicalBusyV1
-- name    : Kyprianou.Ch04.exercise46PrefixCanonicalBusyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:28:42.620304+00:00
-- url     : https://prove2.me/theorems/fef08078-bf43-5889-ac22-8aae0053299c
-- title:
--   The first arrival is a canonical busy start and no other precedes recovery
-- statement:
--   The first jump has left value a and supremum a. Before or at recovery every path value is bounded by a, hence the running supremum is a after arrival. Any other busy start there would be a negative jump at prelevel a, excluded by hypothesis.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise46PrefixCanonicalBusyV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P G) (w : Omega) (a : NNReal) (ha : 0 < a)
    (hJump : L.X a w < Function.leftLim (fun u : NNReal => L.X u w) a)
    (hPrefix : ∀ s : NNReal, s < a → L.X s w = (s : Real))
    (hBound : ∀ s : NNReal, L.X s w ≤ (s : Real))
    (hBefore : ∀ u : NNReal, 0 < u → u < a →
      L.X u w = Function.leftLim (fun v : NNReal => L.X v w) u)
    (hNo : ∀ t : NNReal, 0 < t → a < t →
      Function.leftLim (fun u : NNReal => L.X u w) t = (a : Real) →
      ¬ L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t) :
    let S : Set NNReal := {t | 0 < t ∧ sSup ((fun u => L.X u w) '' Iic t) =
      Function.leftLim (fun u : NNReal => L.X u w) t ∧
      L.X t w < Function.leftLim (fun u : NNReal => L.X u w) t}
    let R : WithTop NNReal := ⨅ t : NNReal, if (a : WithTop NNReal) < (t : WithTop NNReal) ∧
      (a : Real) < L.X t w then (t : WithTop NNReal) else ⊤
    a ∈ S ∧ (∀ t ∈ S, (t : WithTop NNReal) ≤ R → t = a) := by
  sorry
