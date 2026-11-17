-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenSupRatioBounded
-- name    : Kyprianou.Ch07.kestenSupRatioBounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:32:07.17602+00:00
-- url     : https://prove2.me/theorems/222bcba7-ed8e-4f94-bc54-0959d421e19c
-- title:
--   Kesten: finite real supremum bounds every ratio under a common majorant
-- statement:
--   If every convolution-tail ratio at a positive threshold is bounded above by a common finite real C, then the exact real supremum over these ratios lies between each particular ratio and C. The proof uses the nonempty bounded-above supremum in the real line. This is the order-theoretic step constructing each term of Kesten’s envelope sequence.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed p.201, original PDF p.210, supremum definition of ξ_n. Full proof reached pinned private remote Lean sentinel, job 3c63d629-9ee5-4883-b30e-35d359bddf7e.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenSupRatioBounded
    (G : Measure Real) (n : Nat) (C : Real)
    (hC : ∀ x : Real, 0 < x →
      ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
        (G (Set.Ioi x)).toReal ≤ C)
    (x : Real) (hx : 0 < x) :
    let S : Set Real := { y | ∃ z : Real, 0 < z ∧
      y = ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi z)).toReal /
        (G (Set.Ioi z)).toReal };
    ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
      (G (Set.Ioi x)).toReal ≤ sSup S ∧
      sSup S ≤ C := by
  sorry
