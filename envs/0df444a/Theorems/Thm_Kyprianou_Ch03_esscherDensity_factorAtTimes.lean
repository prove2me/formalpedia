-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherDensity_factorAtTimes
-- name    : Kyprianou.Ch03.esscherDensity_factorAtTimes
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T19:12:16.195596+00:00
-- url     : https://prove2.me/theorems/e58c8217-8a5b-49cd-ac0f-203a9dbd4406
-- title:
--   Esscher density multiplicative increment factorisation
-- statement:
--   The Esscher density at a time factors as its earlier value times a normalized increment exponential.
-- source:
--   Kyprianou (2006) Chapter 3 Esscher change of measure

import Mathlib
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem esscherDensity_factorAtTimes
    {Omega : Type} (X : NNReal -> Omega -> Real)
    (beta k : Real) (s t : NNReal) (omega : Omega) :
    esscherDensity X beta k t omega =
      esscherDensity X beta k s omega *
        Real.exp (beta * (X t omega - X s omega) -
          k * ((t : Real) - (s : Real))) := by
  sorry

end Kyprianou.Ch03
