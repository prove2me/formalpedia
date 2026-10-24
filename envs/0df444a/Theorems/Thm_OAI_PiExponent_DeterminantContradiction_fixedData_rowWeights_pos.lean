-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_fixedData_rowWeights_pos
-- name    : OAI.PiExponent.DeterminantContradiction.fixedData_rowWeights_pos
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:24:50.559982+00:00
-- url     : https://prove2.me/theorems/ed918ddf-f376-4d85-8372-55c9967db44d
-- title:
--   Positivity of fixed-data row weights
-- statement:
--   Every row weight from admissible fixed data is positive. The first coordinate uses `d.v0_pos`; each remaining coordinate uses `qᵢ ≥ 2`, positivity of `log qᵢ`, positivity of its natural ceiling, and `d.base.theta_pos`. A proof splits the index with `Fin.cases` and applies those hypotheses.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.fixedData_rowWeights_pos
    (nu : ℝ) (d : FixedData nu) :
    ∀ i : Fin (d.m + 1),
      0 < InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i := by sorry
