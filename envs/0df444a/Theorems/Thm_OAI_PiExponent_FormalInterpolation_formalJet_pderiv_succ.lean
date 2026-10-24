-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_pderiv_succ
-- name    : OAI.PiExponent.FormalInterpolation.formalJet_pderiv_succ
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:03:09.49434+00:00
-- url     : https://prove2.me/theorems/c8932340-c67b-41f7-93fa-428d447e374d
-- title:
--   Formal jet commutes with a successor partial derivative
-- statement:
--   For every polynomial, substituting the formal jet and then taking the partial derivative in a successor variable agrees with first taking the polynomial partial derivative and then substituting the formal jet.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.formalJet_pderiv_succ {m : Nat} (c : Fin m → Complex) (i : Fin m) (F : MvPolynomial (Fin (m + 1)) Complex) : formalJet c (MvPolynomial.pderiv i.succ F) = MvPowerSeries.pderiv Complex i.succ (formalJet c F) := by sorry
