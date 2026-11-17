-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroACountIndependentOfThreeArbitraryOutsideMarksSameTime
-- name    : Kyprianou.Ch06.zeroACountIndependentOfThreeArbitraryOutsideMarksSameTime
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:46:06.690322+00:00
-- url     : https://prove2.me/theorems/5ba7b494-40d3-475b-a380-5fc46f7b1133
-- title:
--   Zero A-count independent of three arbitrarily overlapping outside mark counts observed at the same time
-- statement:
--   For the exact Chapter 6 marked Poisson point process and three arbitrarily overlapping, measurable, finite-intensity outside-A mark sets B,C,D at a common observation time u, the original zero A-count at any time r is independent of the simultaneous three-count cylinder at arbitrary count levels k,l,q. The source a.e spatial additivity decomposes B,C,D into seven disjoint Venn mark atoms; the separately Proved valid/compatible/finitely intense/outside-A certificates and the Proved finite-rectangle observable independence yield the result. This includes all positive-intensity three-way intersections with no strengthened stochastic assumptions.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroACountIndependentOfThreeArbitraryOutsideMarksSameTime
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B C D : Set E) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hD : MeasurableSet D)
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hAD : Disjoint A D)
    (hFA : n A < ⊤) (hFB : n B < ⊤)
    (hFC : n C < ⊤) (hFD : n D < ⊤)
    (r u : NNReal) (k l q : Nat) :
    P {omega | N omega r A = 0 ∧
      N omega u B = k ∧ N omega u C = l ∧
      N omega u D = q} =
    P {omega | N omega r A = 0} *
    P {omega | N omega u B = k ∧
      N omega u C = l ∧ N omega u D = q} := by sorry
