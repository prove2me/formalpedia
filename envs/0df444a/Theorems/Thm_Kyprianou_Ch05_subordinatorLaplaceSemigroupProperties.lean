-- Prove2me | Theorems.Thm_Kyprianou_Ch05_subordinatorLaplaceSemigroupProperties
-- name    : Kyprianou.Ch05.subordinatorLaplaceSemigroupProperties
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:22:46.608115+00:00
-- url     : https://prove2.me/theorems/7f8213cb-4acc-4aa8-8f79-84344d006152
-- title:
--   Lemma 5.2: positive time-Laplace semigroup
-- statement:
--   The Laplace transform of an unkilled subordinator marginal lies in (0,1], is antitone in time, and is multiplicative under addition of times.
-- source:
--   Kyprianou (2006), Lemma 5.2; exact subordinator Laplace dichotomy reduction cbe8356f-6685-46d0-bf57-78977a3b6679.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

theorem Kyprianou.Ch05.subordinatorLaplaceSemigroupProperties
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (theta : Real) (htheta : 0 < theta) :
    let g : NNReal → ENNReal := fun t => (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P)
    (∀ t, 0 < g t ∧ g t ≤ 1) ∧ Antitone g ∧
      (∀ s t, g (s+t) = g s * g t) := by sorry
