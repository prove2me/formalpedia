-- Prove2me | Theorems.Thm_OAI_CurrentProjection_actualRowSourceRefinement
-- name    : OAI.CurrentProjection.actualRowSourceRefinement
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:32.569989+00:00
-- url     : https://prove2.me/theorems/c2ffe9ae-52ae-4d4a-b37c-b6b5256feaad
-- statement:
--   The theorem states that, for dimension d and m rows, countable measurable spaces W and E with measurable singletons, and a probability measure P on ((S×W)×Rows), where S is the unit sphere in ℝ^d and Rows is m-tuples of vectors in ℝ^d, adding a measurable label e(s,w) ∈ E to the discrete variable W does not change the actual conditional row information. Assume ν is a probability measure on the sphere such that, after moving the rows to the outer coordinate, the (sphere, rows) marginal of P equals the product of ν with the law of m independent standard Gaussian vectors in ℝ^d; assume e : S×W → E is measurable; and assume the Shannon entropy of the law of the augmented discrete variable (w, e(s,w)) under the transformed measure is not infinite. Here the transformed measure is the pushforward of P under ((s,w),g) ↦ ((s,(w,e(s,w))),g). Then actualConditionalRowInformation of this pushforward equals actualConditionalRowInformation of P. That quantity is defined as the conditional mutual information, given the sphere coordinate s, between the rows g and the discrete variable W, namely the KL divergence from the joint law of (s,(g,W)) to the law in which g and W are conditionally independent given s with the same conditional marginals.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianReplacement.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianReplacement.lean; bytes 25060..25742
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GaussianReplacement

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InformationTheory

open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

namespace CurrentProjection

theorem actualRowSourceRefinement {d m : ℕ} {W E : Type*} [MeasurableSpace W]
    [MeasurableSpace E] [Countable W] [MeasurableSingletonClass W]
    [Countable E] [MeasurableSingletonClass E]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (e : Sphere d×W → E) (he : Measurable e)
    (hEntropy : shannonEntropy
      ((P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))).map swapLast).snd ≠ ∞) :
    actualConditionalRowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) =
      actualConditionalRowInformation P := by
  sorry

end CurrentProjection
end
end OAI
