-- Prove2me | Theorems.Thm_Kyprianou_Ch05_exercise55CompleteSpaceFutureFactor
-- name    : Kyprianou.Ch05.exercise55CompleteSpaceFutureFactor
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T16:08:30.333066+00:00
-- url     : https://prove2.me/theorems/ad0b15cc-2863-4e44-ab6f-31c93364f198
-- title:
--   Complete-space discounted stopped future factor and measurable integrands
-- statement:
--   On a complete probability space, the strong Markov factorisation of the strict upper passage gives the discounted future moment. Both stopped integrands are measurable by completed natural filtration stopped-state results, right continuity, and shifted clock measurability. The time zero case gives the stopped moment measurability.
-- source:
--   Kyprianou (2006), Exercise 5.5(i); Chapter 3 Theorems 3.1 and 3.3.

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Definitions.Def_Kyprianou_Ch05_CompleteStrictPassageMarkovLaw
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
open Classical

theorem Kyprianou.Ch05.exercise55CompleteSpaceFutureFactor
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] [P.IsComplete]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (Phi : Real → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess Y P)
    (hCoord : ∀ t : NNReal, Measurable (Y t))
    (hMono : ∀ᵐ w ∂P, Monotone (fun t : NNReal => Y t w))
    (hDeath : ∀ w, death w = ⊤)
    (hLaplace : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ w, Real.exp (-theta * Y t w) ∂P) = Real.exp (-(t : Real) * Phi theta))
    (hMarkov : CompleteStrictPassageMarkovLaw) :
  (∀ alpha beta x : Real, 0 ≤ alpha → 0 ≤ beta → 0 < x →
      ∀ s : NNReal,
        Measurable (fun w : Omega =>
          if PassageFinite Y death x w then
            Real.exp (-alpha * ((passageFiniteTime Y death x w + s : NNReal) : Real)
              - beta * Y (passageFiniteTime Y death x w + s) w)
          else 0)) ∧
  (∀ alpha beta x : Real, 0 ≤ alpha → 0 ≤ beta → 0 < x →
      ∀ s : NNReal,
        (∫ w : Omega,
          if PassageFinite Y death x w then
            Real.exp (-alpha * ((passageFiniteTime Y death x w + s : NNReal) : Real)
              - beta * Y (passageFiniteTime Y death x w + s) w)
          else 0 ∂P) =
        Real.exp (-(s : Real) * (alpha + Phi beta)) *
          exponentialFirstPassageMoment P Y death alpha beta x) := by
  sorry
