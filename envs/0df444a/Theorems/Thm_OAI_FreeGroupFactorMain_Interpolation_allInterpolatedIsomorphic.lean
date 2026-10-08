-- Prove2me | Theorems.Thm_OAI_FreeGroupFactorMain_Interpolation_allInterpolatedIsomorphic
-- name    : OAI.FreeGroupFactorMain.Interpolation.allInterpolatedIsomorphic
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:41.691249+00:00
-- url     : https://prove2.me/theorems/9af858a6-bb05-4f0a-aa34-c7f88d021dfd
-- statement:
--   The theorem states that for any two extended nonnegative real parameters r and s, both strictly greater than 1 (so either may be infinite), the interpolated factors attached to r and s are isomorphic as C*-algebras with trace and topology, meaning the type of normal tracial equivalences between them is nonempty. The interpolated factor at a parameter is chosen by cases: for r = ∞ it is the group von Neumann algebra of the free group on countably many generators; for r equal to a natural number n it is the group von Neumann algebra of the free group on n generators; otherwise it is the corner pAp of the stabilization of the rank-two free group algebra, cut down by a selected star projection p whose stabilized projection trace is the real number 1/√(r−1), with the trace being the stabilized trace rescaled by the inverse of that value. Each carries its canonical trace or this rescaled trace and an ultraweak-type topology. A NormalTracialEquiv between two such models consists of a ℂ-linear star-algebra isomorphism that preserves the traces and is continuous in both directions for the given topologies.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/InterpolatedFactors.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/InterpolatedFactors.lean; bytes 8345..8569
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_InterpolatedFactors

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_42 u_43

namespace FreeGroupFactorMain.Interpolation

open Amplification

open scoped ENNReal

theorem allInterpolatedIsomorphic (r s : ℝ≥0∞) (hr : 1<r) (hs : 1<s) :
    Nonempty (NormalTracialEquiv (interpolatedTrace r) (interpolatedTrace s)
      (interpolatedTopology r) (interpolatedTopology s)) := by
  sorry

end FreeGroupFactorMain.Interpolation
end
end OAI
