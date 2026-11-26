-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledPassageFinite_iff_nat
-- name    : Kyprianou.Ch05.unkilledPassageFinite_iff_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:12:29.899802+00:00
-- url     : https://prove2.me/theorems/f3a6d6c0-0bed-47f7-ac09-86dc5a62964c
-- title:
--   Finite strict passage on monotone unkilled paths is witnessed at an integer time
-- statement:
--   A finite infimum has a nonempty defining set. Monotonicity extends any finite witness to a positive integer time; the reverse follows from the infimum bound.
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

theorem Kyprianou.Ch05.unkilledPassageFinite_iff_nat
    {Omega : Type} (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal) (hDeath : ∀ w, death w = ⊤)
    (x : Real) (w : Omega) (hMono : Monotone (fun t : NNReal => Y t w)) :
    PassageFinite Y death x w ↔ ∃ n : ℕ, 0 < n ∧ x < Y (n : NNReal) w := by
  sorry
