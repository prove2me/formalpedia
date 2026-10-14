-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCoordinate_formalJet_has_weighted_support
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_formalJet_has_weighted_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T06:16:47.394461+00:00
-- url     : https://prove2.me/theorems/5a5b15b5-2332-406e-99a9-e41886b3529d
-- title:
--   Weighted support of an unpowered logarithmic coordinate
-- statement:
--   Under nonnegative weights and the truncation inequalities, each unpowered logarithmic coordinate has formal-jet coefficients only at weighted degree at least the weight of its corresponding variable.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/CompactJetPolynomial.lean

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_formalJet_has_weighted_support
    {m : Nat} (c : Fin m -> Complex) (T : Fin m -> Nat)
    (v : Fin (m + 1) -> Real)
    (hv : forall i, 0 <= v i)
    (hT : forall i, v i.succ <= (T i : Real) * v 0)
    (i : Fin (m + 1)) :
    FormalInterpolation.hasWeightedSupport v (v i)
      (FormalInterpolation.formalJet c
        (FormalInterpolation.logarithmicCoordinate c T i)) := by sorry
