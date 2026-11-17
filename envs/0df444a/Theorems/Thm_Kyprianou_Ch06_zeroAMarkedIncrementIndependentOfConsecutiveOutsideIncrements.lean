-- Prove2me | Theorems.Thm_Kyprianou_Ch06_zeroAMarkedIncrementIndependentOfConsecutiveOutsideIncrements
-- name    : Kyprianou.Ch06.zeroAMarkedIncrementIndependentOfConsecutiveOutsideIncrements
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T21:07:32.353809+00:00
-- url     : https://prove2.me/theorems/372708c4-f9f3-4789-baa3-6e2c664953af
-- title:
--   Zero marked-Poisson A increment independent of two consecutive outside B increments
-- statement:
--   For any marked Poisson process satisfying the original Chapter 6 finite-rectangle law, if A and B are measurable finite-intensity and disjoint, then the zero A-increment count on any interval from time zero to r is independent of the joint B-increment counts on consecutive intervals [0,s] and (s,t], for s≤t and arbitrary count values. Derive the three-rectangle joint Poisson product directly from the source PPP law, the one-rectangle A marginal from the same law, and the two-rectangle B joint marginal from the independently Proved consecutive-interval theorem. No strengthened mark or independent-increment hypotheses.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
open MeasureTheory Filter
open scoped NNReal ENNReal
open Kyprianou.Ch06
set_option autoImplicit false

theorem Kyprianou.Ch06.zeroAMarkedIncrementIndependentOfConsecutiveOutsideIncrements
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (A B : Set E) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (hFA : n A < ⊤) (hFB : n B < ⊤)
    (r s t : NNReal) (hst : s ≤ t) (k l : Nat) :
    P {omega | N omega r A - N omega 0 A = 0 ∧
      N omega s B - N omega 0 B = k ∧
      N omega t B - N omega s B = l} =
    P {omega | N omega r A - N omega 0 A = 0} *
    P {omega | N omega s B - N omega 0 B = k ∧
      N omega t B - N omega s B = l} := by sorry
