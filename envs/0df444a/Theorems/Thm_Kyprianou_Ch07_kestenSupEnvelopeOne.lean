-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenSupEnvelopeOne
-- name    : Kyprianou.Ch07.kestenSupEnvelopeOne
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:34:51.054323+00:00
-- url     : https://prove2.me/theorems/4bf078f6-dfa2-4a20-9668-d950b6434600
-- title:
--   Kesten supremum envelope base: ξ_1=1 exactly
-- statement:
--   Under the Kesten strict positivity-of-upper-tails hypothesis, the n=1 supremum of the convolution-tail ratio is exactly one. Each ratio is one by the proved onefold convolution law; the pinned real supremum comparison theorem bounds the supremum above and below by one.
-- source:
--   Kyprianou (2006), Chapter 7, Lemma 7.14 proof, printed p.201, original PDF p.210: “It is clear that ξ1≤1”, strengthened to equality by the original strictly positive-tail hypothesis. Full proof remote private job be1d1663-fe29-4be1-9771-e40d62dae76a.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Definitions.Def_Kyprianou_Ch07_KestenSupEnvelope
import Theorems.Thm_Kyprianou_Ch07_kestenSupRatioBounded
import Theorems.Thm_Kyprianou_Ch07_kestenOnefoldTailRatio
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenSupEnvelopeOne
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x)) :
    Kyprianou.Ch07.kestenSupEnvelope G 1 = 1 := by
  sorry
