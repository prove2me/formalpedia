-- Prove2me | Theorems.Thm_Kyprianou_Ch05_unkilledStrictUpcrossing_eq_firstHittingTime
-- name    : Kyprianou.Ch05.unkilledStrictUpcrossing_eq_firstHittingTime
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T16:12:40.745801+00:00
-- url     : https://prove2.me/theorems/f60d10e4-a80e-4117-9670-bfda049e9fb4
-- title:
--   Unkilled strict upcrossing is Chapter 3 first hitting time
-- statement:
--   The clocks are exactly the same infimum when death is infinite.
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

theorem Kyprianou.Ch05.unkilledStrictUpcrossing_eq_firstHittingTime
    {Omega : Type} (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal) (hDeath : ∀ w, death w = ⊤)
    (x : Real) (w : Omega) :
    strictUpcrossing Y death x w = Kyprianou.Ch03.firstHittingTime Y (Set.Ioi x) w := by
  sorry
