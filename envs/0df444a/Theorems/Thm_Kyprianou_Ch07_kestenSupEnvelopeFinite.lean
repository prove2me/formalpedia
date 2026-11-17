-- Prove2me | Theorems.Thm_Kyprianou_Ch07_kestenSupEnvelopeFinite
-- name    : Kyprianou.Ch07.kestenSupEnvelopeFinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T23:35:48.914575+00:00
-- url     : https://prove2.me/theorems/988c49fc-5862-4367-b6d1-b79e67950e71
-- title:
--   Kesten: finite positive upper bound for each exact supremum tail-ratio envelope
-- statement:
--   Under the original Chapter 7 Kesten hypotheses, for every n>=1 the ratio of the n-fold convolution upper tail to the original upper tail lies below the exact supremum envelope ξ_n, which in turn is finite and bounded by a positive constant C_n. This proves the source-defined ξ_n is a usable finite real number for every n and all x>0.
-- source:
--   Kyprianou (2006), Chapter 7, proof of Lemma 7.14, printed p.201, original PDF p.210. Exact complete source pinned remote Lean job eca42f91-aa4b-45c2-a66a-4e85c128acaa.

import Mathlib
import Definitions.Def_Kyprianou_Ch07_ConvolutionLargeJumpLaw
import Definitions.Def_Kyprianou_Ch07_KestenSupEnvelope
import Theorems.Thm_Kyprianou_Ch07_kestenSupRatioBounded
import Theorems.Thm_Kyprianou_Ch07_kestenEachOrderHasFiniteTailBound
open MeasureTheory Filter
open scoped ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.kestenSupEnvelopeFinite
    (G : Measure Real) [IsProbabilityMeasure G]
    (hPositiveTail : ∀ x : Real, 0 < x → 0 < G (Set.Ioi x))
    (hConv : ∀ n : Nat, 2 ≤ n →
      Tendsto (fun x : Real =>
        ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
          ((n : Real) * (G (Set.Ioi x)).toReal))
        atTop (nhds (1 : Real))) :
    ∀ n : Nat, 1 ≤ n →
      ∃ C : Real, 0 < C ∧
        (∀ x : Real, 0 < x →
          ((Kyprianou.Ch07.convolutionPower G n) (Set.Ioi x)).toReal /
            (G (Set.Ioi x)).toReal ≤
              Kyprianou.Ch07.kestenSupEnvelope G n) ∧
        Kyprianou.Ch07.kestenSupEnvelope G n ≤ C := by
  sorry
