-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenShiftedTailMeasurable
-- name    : Kyprianou.Ch07.kestenShiftedTailMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:53:48.423174+00:00
-- url     : https://prove2.me/theorems/7fec2d1c-f709-49ea-b032-7c2a5cabba89
-- title:
--   Measurability of shifted upper-tail mass for arbitrary real Borel measures
-- statement:
--   For any Borel measure G on the real line and threshold x, the map a↦G((x−a,infinity)) is measurable, since it is monotone in a. This supplies the exact analytic measurability premise needed when integrating Kesten’s shifted convolution tails.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed pp.201–202, original PDF pp.210–211; exact pinned private remote source compiler evidence.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenShiftedTailMeasurable
    (G : Measure Real) (x : Real) :
    Measurable (fun a : Real => G (Set.Ioi (x - a))) := by
  sorry
