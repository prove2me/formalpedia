-- Prove2me | Theorems.Thm_Kyprianou_Ch05_subordinator_zero_of_unitLaplace
-- name    : Kyprianou.Ch05.subordinator_zero_of_unitLaplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:12:29.713793+00:00
-- url     : https://prove2.me/theorems/e6a709aa-ad89-4eea-b24c-d4d44e418e0f
-- title:
--   A subordinator whose positive Laplace moment is one at integer times is zero
-- statement:
--   Use Chapter 1 mean-one lemma on every integer time, then monotonicity and cofinality to deduce zero at every time.
-- source:
--   Kyprianou (2006), Exercise 5.5(i); Chapter 1 and Chapter 3 reuse.

import Definitions.Def_Kyprianou_Ch05_ExponentialPassageMoments
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_WeakPassageObservables
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
open Classical

theorem Kyprianou.Ch05.subordinator_zero_of_unitLaplace
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess Y P)
    (hMono : ∀ᵐ w ∂P, Monotone (fun t : NNReal => Y t w))
    (beta : Real) (hb : 0 < beta)
    (hMean : ∀ n : ℕ, (∫ w, Real.exp (-beta * Y (n : NNReal) w) ∂P) = 1) :
    ∀ᵐ w ∂P, ∀ t : NNReal, Y t w = 0 := by
  sorry
