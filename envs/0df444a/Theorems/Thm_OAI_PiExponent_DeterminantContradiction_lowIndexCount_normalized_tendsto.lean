-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_lowIndexCount_normalized_tendsto
-- name    : OAI.PiExponent.DeterminantContradiction.lowIndexCount_normalized_tendsto
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T06:20:29.872982+00:00
-- url     : https://prove2.me/theorems/ac30f94b-44ad-48b6-8e3d-ff403466555f
-- title:
--   Asymptotic count of low-index exponents
-- statement:
--   For each admissible datum, the non-strict weighted simplex count with cutoff `A H`, divided by `H^m`, tends to its volume coefficient. The admissible denominator weights and `A` are positive; the non-strict boundary changes only a lower-order count. This removes the low-index count asymptotic from the parent. A proof route uses scaled grid boxes and a boundary-volume estimate, independently of the row simplex estimate.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.lowIndexCount_normalized_tendsto (nu : Real) (d : FixedData nu) :
    Tendsto (fun H : Real => (lowIndexCount d H : Real) / H ^ d.m) atTop
      (nhds ((d.base.A : Real) ^ d.m /
        ((d.m.factorial : Real) *
          ∏ i : Fin d.m, MatrixArithmetic.logWeights (finiteDenominators d) i))) := by sorry
