-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCoordinate_formalJet_coeff_support_profile
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_formalJet_coeff_support_profile
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T06:27:18.835319+00:00
-- url     : https://prove2.me/theorems/365a62e4-fec2-41aa-82f8-68bbd1a5b593
-- title:
--   Coefficient support profile of a logarithmic coordinate
-- statement:
--   Every nonzero formal-jet coefficient of a logarithmic coordinate is supported either at its own variable's unit exponent or, for a nonzero coordinate, at a pure zeroth-variable exponent at least its truncation index.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/CompactJetPolynomial.lean

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_formalJet_coeff_support_profile
    {m : Nat} (c : Fin m -> Complex) (T : Fin m -> Nat)
    (i : Fin (m + 1)) (b : Fin (m + 1) -> Nat)
    (hcoeff : MvPowerSeries.coeff (InterpolationMatrix.exponentVector b)
      (FormalInterpolation.formalJet c
        (FormalInterpolation.logarithmicCoordinate c T i)) ≠ 0) :
    (i = 0 /\ b = fun j => if j = 0 then 1 else 0) \/
      (exists k : Fin m, i = k.succ /\
        b = fun j => if j = k.succ then 1 else 0) \/
      (exists k : Fin m, exists n : Nat, i = k.succ /\
        (b = fun j => if j = 0 then n else 0) /\ T k <= n) := by
  sorry
