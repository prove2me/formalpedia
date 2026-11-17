-- Prove2me | Theorems.Thm_Kyprianou_Ch06_fourOverlapSpacetimeRectanglesValid
-- name    : Kyprianou.Ch06.fourOverlapSpacetimeRectanglesValid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:37:06.035727+00:00
-- url     : https://prove2.me/theorems/9748bded-64ec-4eb2-850e-684987bf9003
-- title:
--   Four overlapping-mark space-time rectangles have valid ordered times, measurable marks and finite intensity
-- statement:
--   For arbitrary measurable finite-intensity source marks B,C and s≤t, show that the four rectangles [0,s]×(B\C), [0,s]×(B∩C), [0,s]×(C\B) and (s,t]×C each satisfy the exact Chapter 6 marked-Poisson axiom rectangle validity premises. Intensity bounds come solely from measure monotonicity.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.fourOverlapSpacetimeRectanglesValid
    {E : Type} [MeasurableSpace E]
    (n : Measure E) (B C : Set E)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hFB : n B < ⊤) (hFC : n C < ⊤)
    (s t : NNReal) (hst : s ≤ t) :
    let starts : Fin 4 → NNReal := fun i => if i = 3 then s else 0
    let stops : Fin 4 → NNReal := fun i => if i = 3 then t else s
    let marks : Fin 4 → Set E := fun i =>
      if i = 0 then B \ C else if i = 1 then B ∩ C
        else if i = 2 then C \ B else C
    ∀ i, starts i ≤ stops i ∧
      MeasurableSet (marks i) ∧ n (marks i) < ⊤ := by sorry
