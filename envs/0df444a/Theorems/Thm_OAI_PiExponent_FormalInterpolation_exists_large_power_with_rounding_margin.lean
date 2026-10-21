-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_exists_large_power_with_rounding_margin
-- name    : OAI.PiExponent.FormalInterpolation.exists_large_power_with_rounding_margin
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-20T22:49:51.151099+00:00
-- url     : https://prove2.me/theorems/17cbf93f-4864-44ac-8b00-03af586f98e0
-- title:
--   Choose a power exceeding finitely many coordinate weights
-- statement:
--   For a positive rate gap and any threshold, choose a positive natural number at least that threshold whose scaled gap exceeds all coordinate weights. The finite coordinate set makes one sufficiently large choice work simultaneously, including the vacuous-coordinate case.
-- source:
--   Reduction obligation for OAI.PiExponent.FormalInterpolation.weightedIdealCurveBound_eventual_quotient_representatives (globalInterpolation pillar; weighted compactification / ampleness / Serre vanishing / ordinary Rees recovery argument), split at the interface between the geometric weighted-monic-relations output of the curve criterion and the algebraic weighted division step. (geometric step: curve criterion -> weighted monic relations)

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion

open scoped BigOperators

theorem OAI.PiExponent.FormalInterpolation.exists_large_power_with_rounding_margin
    {d : Nat} (w : Fin d → Rat) (hw : ∀ i, 0 < (w i : Real))
    (a c : Rat) (hca : c < a) (N : Nat) :
    ∃ k : Nat, 0 < k ∧ N ≤ k ∧
      ∀ i, (k : Real) * ((a - c : Rat) : Real) > (w i : Real) := by sorry
