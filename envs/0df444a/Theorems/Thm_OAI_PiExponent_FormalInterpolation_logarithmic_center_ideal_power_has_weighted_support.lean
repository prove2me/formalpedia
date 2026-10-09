-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_center_ideal_power_has_weighted_support
-- name    : OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_has_weighted_support
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T17:10:19.35723+00:00
-- url     : https://prove2.me/theorems/f8010464-5a8a-490d-b9e0-f1ad45f211b2
-- title:
--   Weighted support bound for logarithmic center ideal powers
-- statement:
--   Let v assign a nonnegative weight to each formal-jet coordinate. For a polynomial in the nth power of the logarithmic center ideal, every nonzero coefficient of the formal jet has total weight at least n times R. The truncation bounds control the logarithmic coordinates and the multiplicities e_i.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/CompactJetPolynomial.lean, theorem formalJet_mem_weighted_of_mem_pow

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.logarithmic_center_ideal_power_has_weighted_support
    {m : Nat} (c : Fin m -> Complex) (T : Fin m -> Nat)
    (e : Fin (m + 1) -> Nat) (v : Fin (m + 1) -> Real)
    (hv : forall i, 0 <= v i)
    (hT : forall i, v i.succ <= (T i : Real) * v 0)
    (R : Real) (he : forall i, R <= (e i : Real) * v i)
    (n : Nat) (P : MvPolynomial (Fin (m + 1)) Complex)
    (hP : Membership.mem (FormalInterpolation.logarithmicCenterIdeal c T e ^ n) P)
    (b : Fin (m + 1) -> Nat)
    (hcoeff : Not (MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (FormalInterpolation.formalJet c P) = 0)) :
    (n : Real) * R <= Finset.univ.sum (fun i => (b i : Real) * v i) := by sorry
