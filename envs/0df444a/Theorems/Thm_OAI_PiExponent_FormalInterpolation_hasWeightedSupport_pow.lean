-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_hasWeightedSupport_pow
-- name    : OAI.PiExponent.FormalInterpolation.hasWeightedSupport_pow
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T06:17:08.833199+00:00
-- url     : https://prove2.me/theorems/741113a3-23dd-4782-9ca1-a84366c76f31
-- title:
--   Powers preserve weighted support with scaled threshold
-- statement:
--   For nonnegative variable weights, if a multivariate formal power series has weighted support at threshold $B$, its $n$-th power has weighted support at threshold $nB$.
-- source:
--   Adapted from formalJet_mem_weighted_of_mem_pow in CompactJetPolynomial.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Jets/CompactJetPolynomial.lean

import Definitions.Def_OAI_PiExponent_WeightedSupport

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.hasWeightedSupport_pow
    {m : Nat} (v : Fin (m + 1) -> Real) (B : Real)
    (hv : forall i, 0 <= v i)
    (F : MvPowerSeries (Fin (m + 1)) Complex)
    (hF : FormalInterpolation.hasWeightedSupport v B F) (n : Nat) :
    FormalInterpolation.hasWeightedSupport v ((n : Real) * B) (F ^ n) := by sorry
