-- Prove2me | Theorems.Thm_OAI_CKSMain_schwarzschild_equality_examples
-- name    : OAI.CKSMain.schwarzschild_equality_examples
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:25.537761+00:00
-- url     : https://prove2.me/theorems/10e49548-eee1-4510-9b6e-ec061dc91028
-- statement:
--   The theorem states that for every real mass m > 0 (and every universe level for the auxiliary test surfaces), the defined proposition SchwarzschildExample holds, so an explicit equality example exists on the Schwarzschild exterior, modeled as the product of the radial half-line [0,∞) with the unit sphere in three-dimensional Euclidean space. Precisely, there exist a smooth Riemannian metric g on this exterior, a CKSData structure d for g and the Schwarzschild second-fundamental-form tensor field, and a coefficient atlas A, such that g agrees pointwise with the Schwarzschild spatial metric of mass m; the full set of main-theorem hypotheses holds for g, this tensor, d and A (smooth symmetric tensor, orientability, compact nonempty connected boundary, completeness, the physical dominant-energy condition, timelike Bondi charge, marginal boundary, positive minimum enclosing area, and the absence of additional horizons); the Schwarzschild data admit a horizon-regular advanced-time graph, meaning a smooth injective embedding with prescribed induced metric, unit future normal and induced second form, with horizon time 0 and slope 1/2 at radius 2m; the Bondi mass of d equals m; the minimum enclosing area of g equals 16πm²; and consequently the Bondi mass equals √(minimum enclosing area/(16π)). The proof is admitted (sorry) in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CKSBondiPenrose.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CKSBondiPenrose.lean; bytes 193107..193219
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CKSBondiPenrose_002

noncomputable section

universe u v w u_1 u_2 u_3 u_4 u_5 u_6

namespace OAI.CKSMain

open Set Filter Manifold Bundle CKSLorentz CKSMetricGluing CKSSpatialManifold

open CKSBoundarySurface CKSIntrinsicConstraints CKSSourceExterior

open scoped ContDiff Topology

attribute [local instance] manifold_regular

open CKSSchwarzschild

theorem schwarzschild_equality_examples (m : ℝ) (hm : 0 < m) :
    SchwarzschildExample.{v} m hm := by
  sorry

end OAI.CKSMain
end
