-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_height_add_fractionField_trdeg_toNat
-- name    : OAI.PiExponent.FormalInterpolation.height_add_fractionField_trdeg_toNat
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:58:48.815217+00:00
-- url     : https://prove2.me/theorems/2a216265-7ded-4096-8329-462367751dd2
-- title:
--   Prime height plus fraction-field transcendence degree over naturals
-- statement:
--   For a prime ideal in the polynomial ring in `m + 1` variables over `Complex`, the natural-valued height plus the natural-valued transcendence degree of the quotient’s fraction field equals `m + 1`.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.Ideal.Height

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.height_add_fractionField_trdeg_toNat
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime] :
    P.height.toNat +
      (Algebra.trdeg Complex
        (OAI.PiExponent.FormalInterpolation.logarithmicPrimeField P)).toNat = m + 1 := by sorry
