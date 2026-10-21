-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_rounding_exponents_with_margin
-- name    : OAI.PiExponent.FormalInterpolation.rounding_exponents_with_margin
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T23:00:39.15087+00:00
-- url     : https://prove2.me/theorems/57e27344-f976-4561-aa48-f179a65b9140
-- title:
--   Round weighted exponents within the margin
-- statement:
--   Round each positive weighted threshold upward to a natural exponent. The strict margin ensures that the rounded weighted exponent remains within the upper bound.
-- source:
--   Reduction obligation for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_quotient_representatives (globalInterpolation pillar; weighted compactification / ampleness / Serre vanishing / ordinary Rees recovery argument), split at the interface between the geometric weighted-monic-relations output of the curve criterion and the algebraic weighted division step. (geometric step: curve criterion -> weighted monic relations)

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.rounding_exponents_with_margin
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (c a : Rat) (hc : 0 < c) (hca : c < a)
    (k : Nat) (hk : 0 < k)
    (hmargin : ∀ i, (k : Real) * ((a - c : Rat) : Real) > (w i : Real)) :
    ∃ b : Fin d → Nat,
      (∀ i, 0 < b i) ∧
      (∀ i, (k : Real) * (c : Real) < (w i : Real) * (b i : Real)) ∧
      (∀ i, (w i : Real) * (b i : Real) ≤ (k : Real) * (a : Real)) := by sorry
