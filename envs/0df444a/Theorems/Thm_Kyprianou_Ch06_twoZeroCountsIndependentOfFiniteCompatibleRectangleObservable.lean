-- Prove2me | Theorems.Thm_Kyprianou_Ch06_twoZeroCountsIndependentOfFiniteCompatibleRectangleObservable
-- name    : Kyprianou.Ch06.twoZeroCountsIndependentOfFiniteCompatibleRectangleObservable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T12:26:34.92684+00:00
-- url     : https://prove2.me/theorems/2b5f88e1-3126-4ac8-a565-5d882804284a
-- title:
--   Lemma 6.18: two competing zero-count events independent of arbitrary a.s. finite countable statistics of compatible outside Poisson rectangles
-- statement:
--   The joint event of zero counts in two disjoint finite-intensity marked-Poisson regions is independent of every finite-dimensional countable statistic that almost surely is a deterministic function of the increments in an arbitrary finite compatible outside time-mark rectangle family. This directly covers overlapping outside regions and independently observed times through the previously Proved outside-count vector representation.
-- source:
--   Kyprianou (2006), Lemma 6.18, pp.160–161, complete first-mark independence from finite-dimensional observations of the outside marked process.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_twoZeroCountsIndependentOfFiniteCompatibleOutsideRectangles
import Theorems.Thm_Kyprianou_Ch06_independentEventOfAlmostSureCountableStatistic
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.twoZeroCountsIndependentOfFiniteCompatibleRectangleObservable
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (B D : Set E) (hB : MeasurableSet B) (hD : MeasurableSet D)
    (hBD : Disjoint B D) (hFB : n B < ⊤) (hFD : n D < ⊤)
    (m p : Nat) (starts stops : Fin m → NNReal)
    (C : Fin m → Set E)
    (hValid : ∀ i, starts i ≤ stops i ∧
      MeasurableSet (C i) ∧ n (C i) < ⊤)
    (hBC : ∀ i, Disjoint B (C i))
    (hDC : ∀ i, Disjoint D (C i))
    (hSep : ∀ i j : Fin m, i ≠ j →
      stops i ≤ starts j ∨ stops j ≤ starts i ∨
      Disjoint (C i) (C j))
    (s t : NNReal) (Y : Omega → Fin p → Nat)
    (f : (Fin m → Nat) → Fin p → Nat)
    (hAe : ∀ᵐ omega ∂P,
      Y omega = f (fun i =>
        N omega (stops i) (C i) - N omega (starts i) (C i)))
    (levels : Fin p → Nat) :
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0 ∧
      Y omega = levels} =
    P {omega |
      N omega s B - N omega 0 B = 0 ∧
      N omega t D - N omega 0 D = 0} *
    P {omega | Y omega = levels} := by sorry
