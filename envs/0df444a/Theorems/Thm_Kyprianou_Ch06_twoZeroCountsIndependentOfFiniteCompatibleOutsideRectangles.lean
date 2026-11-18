-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoZeroCountsIndependentOfFiniteCompatibleOutsideRectangles
-- name    : Kyprianou.Ch06.twoZeroCountsIndependentOfFiniteCompatibleOutsideRectangles
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:23:38.188235+00:00
-- url     : https://prove2.me/theorems/497317bd-44db-4dc6-b90f-3090d4c2442a
-- title:
--   Lemma 6.18: joint zero counts in competing mark regions are independent of any compatible outside marked rectangle count vector
-- statement:
--   For disjoint finite-intensity Poisson mark regions B and D, the joint event of zero counts in B at time s and in D at time t is independent of the joint counts over any finite family of compatible outside time-mark rectangles, even when the outside marks overlap spatially at separated times.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, joint independence of competing first-mark clocks from the outside point process via finite rectangular Poisson count laws.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoZeroCountsPlusFiniteCompatibleRectanglesPoissonProduct
import Theorems.Thm_Kyprianou_Ch06_twoDisjointMarkedPoissonRectangles
open MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoZeroCountsIndependentOfFiniteCompatibleOutsideRectangles
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (m : Nat) (starts stops : Fin m → NNReal)
    (C : Fin m → Set E) (counts : Fin m → Nat)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (C i) ∧ n (C i) < ⊤)
    (hBC : ∀ i, Disjoint B (C i))
    (hDC : ∀ i, Disjoint D (C i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (C i) (C j))
    (s t : NNReal) :
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0 ∧
      ∀ i : Fin m,
        N omega (stops i) (C i) -
          N omega (starts i) (C i) = counts i} =
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0} *
    P {omega | ∀ i : Fin m,
        N omega (stops i) (C i) -
          N omega (starts i) (C i) = counts i} := by sorry
