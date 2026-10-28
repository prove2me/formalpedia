-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_quotient_trdeg_lt_aleph0
-- name    : OAI.PiExponent.FormalInterpolation.quotient_trdeg_lt_aleph0
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T00:52:40.653424+00:00
-- url     : https://prove2.me/theorems/8c54b65c-e603-4dd7-ac48-2b4e69ff1185
-- title:
--   Finite transcendence degree of the polynomial quotient
-- statement:
--   The quotient has finite transcendence degree because a polynomial algebra on the finite type `Fin (Nat.succ m)` is finite type over Complex, and finite type descends to quotients. A proof route is to infer the quotient’s finite type algebra instance and apply Mathlib’s `trdeg_lt_aleph0_of_finiteType`. The strict bound holds also for m = 0; the prime assumption is retained to match the parent and its quotient-domain setting.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

theorem OAI.PiExponent.FormalInterpolation.quotient_trdeg_lt_aleph0 {m : Nat} (P : Ideal (MvPolynomial (Fin (Nat.succ m)) Complex)) [P.IsPrime] : Algebra.trdeg Complex (MvPolynomial (Fin (Nat.succ m)) Complex ⧸ P) < Cardinal.aleph0 := by sorry
