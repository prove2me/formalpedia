-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_logarithmic_center_generator_has_weighted_support
-- name    : OAI.PiExponent.FormalInterpolation.formalJet_logarithmic_center_generator_has_weighted_support
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-08T18:32:12.512846+00:00
-- url     : https://prove2.me/theorems/2e74afe7-a31a-4bb2-ab26-676ea22e64aa
-- title:
--   Weighted support of logarithmic center generators
-- statement:
--   Each powered logarithmic coordinate has no nonzero formal-jet coefficient below weighted degree R. The truncation condition places the logarithmic tail at the weight of its corresponding variable, and the exponent bound supplies the factor R.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/CompactJetPolynomial.lean

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.formalJet_logarithmic_center_generator_has_weighted_support
    {m : Nat} (c : Fin m -> Complex) (T : Fin m -> Nat)
    (e : Fin (m + 1) -> Nat) (v : Fin (m + 1) -> Real)
    (hv : forall i, 0 <= v i)
    (hT : forall i, v i.succ <= (T i : Real) * v 0)
    (R : Real) (he : forall i, R <= (e i : Real) * v i)
    (i : Fin (m + 1)) :
    FormalInterpolation.hasWeightedSupport v R
      (FormalInterpolation.formalJet c
        (FormalInterpolation.logarithmicCoordinate c T i ^ e i)) := by sorry
