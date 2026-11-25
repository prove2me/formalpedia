-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleRegulatorCrossingFromFiniteV1
-- name    : Kyprianou.Ch04.idleRegulatorCrossingFromFiniteV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-25T00:25:01.667963+00:00
-- url     : https://prove2.me/theorems/c4901491-8ea5-4258-b8a7-39a4002ef976
-- title:
--   Deterministic strict tail crossing from the finite horizon identity
-- statement:
--   The strict inequality against an iSup holds at some finite horizon. Positive finite drift permits rescaling, and each finite path supremum is bounded above by the linear drift. A strict inequality below the supremum is witnessed by an actual path value; conversely any crossing lies in an integer horizon.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1; deterministic regulator calculus.

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.idleRegulatorCrossingFromFiniteV1
    (f : NNReal → Real) (d w : Real) (hd : 0 < d) (hw : 0 ≤ w)
    (hf0 : f 0 = 0)
    (hf : ∀ s t : NNReal, s ≤ t → f t - f s ≤ d * ((t : Real) - (s : Real)))
    (I : Nat → ENNReal)
    (hI : ∀ n : Nat, ENNReal.ofReal (max w (sSup (f '' Iic (n : NNReal))) - w) =
      ENNReal.ofReal d * I n) :
    ∀ x : Real, 0 ≤ x → (ENNReal.ofReal x < ⨆ n, I n ↔
      ∃ t : NNReal, w + d * x < f t) := by
  sorry
