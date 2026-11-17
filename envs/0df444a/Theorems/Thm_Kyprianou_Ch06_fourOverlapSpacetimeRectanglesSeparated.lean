-- Prove2me | Theorems.Thm_Kyprianou_Ch06_fourOverlapSpacetimeRectanglesSeparated
-- name    : Kyprianou.Ch06.fourOverlapSpacetimeRectanglesSeparated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:37:11.411312+00:00
-- url     : https://prove2.me/theorems/a3812eda-4110-464b-bf47-820c0c440ef0
-- title:
--   Four time-split overlapping-mark rectangles satisfy pairwise source Poisson compatibility
-- statement:
--   The source Chapter 6 marked-Poisson compatibility condition holds for the four rectangles formed by three disjoint spatial atoms B\C, B∩C, C\B on [0,s] and the full C mark set on (s,t]. The final rectangle may spatially overlap previous atoms but its time interval is disjoint from theirs.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.fourOverlapSpacetimeRectanglesSeparated
    {E : Type} [MeasurableSpace E]
    (B C : Set E) (s t : NNReal) (hst : s ≤ t) :
    let starts : Fin 4 → NNReal := fun i => if i = 3 then s else 0
    let stops : Fin 4 → NNReal := fun i => if i = 3 then t else s
    let marks : Fin 4 → Set E := fun i =>
      if i = 0 then B \ C else if i = 1 then B ∩ C
        else if i = 2 then C \ B else C
    ∀ i j : Fin 4, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (marks i) (marks j) := by sorry
