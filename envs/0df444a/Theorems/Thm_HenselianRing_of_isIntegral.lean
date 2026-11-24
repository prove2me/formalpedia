-- Prove2me | Theorems.Thm_HenselianRing_of_isIntegral
-- name    : HenselianRing.of_isIntegral
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T23:07:01.781297+00:00
-- url     : https://prove2.me/theorems/22ae7468-8d2c-4266-bce9-1917162516d2
-- title:
--   Stability of henselian pairs under integral base change
-- statement:
--   If $(A,I)$ is a henselian pair and $A	o B$ is integral, then $(B,IB)$ is henselian.
-- source:
--   Stacks Project, Lemma 15.11.8, https://stacks.math.columbia.edu/tag/09XK.

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

set_option autoImplicit false
universe u

theorem HenselianRing.of_isIntegral
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A)
    [HenselianRing A I] (_ : f.IsIntegral) : HenselianRing B (I.map f) := by sorry
