-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_component_local_length_mono
-- name    : OAI.PiExponent.FormalInterpolation.component_local_length_mono
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-24T21:28:14.704991+00:00
-- url     : https://prove2.me/theorems/2b8e0df4-90f9-43f7-83f2-479869f641ed
-- title:
--   Local component length grows under ideal containment
-- statement:
--   If the local quotient by `I` at a prime has finite length `L` and `J ≤ I`, then the local quotient by `J` also has finite length, at least `L`.

import Definitions.Def_OAI_PiExponent_ComponentLocalLength
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.AtPrime.Basic

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.component_local_length_mono
    {R : Type*} [CommRing R]
    (J I P : Ideal R) [P.IsPrime]
    (L : Nat)
    (hI : componentLocalLength I P = (L : ENat))
    (hJI : J ≤ I) :
    ∃ M : Nat,
      componentLocalLength J P = (M : ENat) ∧ L ≤ M := by sorry
