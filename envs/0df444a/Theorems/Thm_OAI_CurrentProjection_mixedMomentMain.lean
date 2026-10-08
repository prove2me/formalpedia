-- Prove2me | Theorems.Thm_OAI_CurrentProjection_mixedMomentMain
-- name    : OAI.CurrentProjection.mixedMomentMain
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:33.231819+00:00
-- url     : https://prove2.me/theorems/7a423317-8987-434a-8746-367266473c9b
-- statement:
--   The theorem states that the defined proposition MixedMomentMain holds. Work on the unit sphere S in R^d with i.i.d. standard Gaussian rows; for rows g₁,…,g_k the label of a point s is the vector (⟨s,g_i⟩)_i. For a measure ρ on S, rows g, target y in R^k and δ>0, the cube average is (2δ)^(−k) times the ρ-measure of the points u whose labels satisfy |⟨u,g_i⟩−y_i|≤δ for all i; the exact density is the limit of these averages along δ=1/j when that limit exists, and 0 otherwise. LocalGrowth(ρ,a,B) says every closed ball of radius t>0 around any z in R^d has ρ-measure at most B·t^a. Dimensions (d,m,r,q) are admissible if m,r,q≥1, m+r<d−1 and r−(q−1)≥1 (natural-number subtraction), and the moment constant is ofReal(exp(C·d)·B·(1+max(log(D/B),0))). The statement is that there is a constant C>0 such that for all admissible (d,m,r,q), every finite measure ρ on S, and all B,D>0 with LocalGrowth(ρ,m+r,B) and LocalGrowth(ρ,d−1,D), two things hold. First, for every s in S and every δ>0, integrating over m Gaussian rows X the q-th power of the integral over r further Gaussian rows Z of the cube average of ρ at the concatenated rows (X,Z) and target the label of s, the result is at most the q-th power of the moment constant. Second, if ρ is absolutely continuous with respect to the uniform probability measure on S, there is a measurable ρ-null set E such that for every s outside E: for almost every (m+r)-row Gaussian G, the cube averages at the label of s converge as δ→0+ to the exact density; the same q-th moment bound holds with the exact density in place of the cube average; and if ρ≠0, then for almost every G the exact density is strictly positive and finite.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianReplacement.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianReplacement.lean; bytes 22013..22068
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GaussianReplacement

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InformationTheory

open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

namespace CurrentProjection

theorem mixedMomentMain : MixedMomentMain := by
  sorry

end CurrentProjection
end
end OAI
