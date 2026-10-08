-- Prove2me | Theorems.Thm_OAI_CurrentProjection_actualRowRefinement
-- name    : OAI.CurrentProjection.actualRowRefinement
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:32.258538+00:00
-- url     : https://prove2.me/theorems/3f72ada8-1734-4a26-845b-74f0ef3d56d1
-- statement:
--   The theorem states that, for dimension d, row count m, countable discrete measurable spaces W and E (countable with measurable singletons), a probability measure P on ((Sphere d × W) × Rows m d), where Sphere d is the unit sphere in d-dimensional Euclidean space and Rows m d is m-tuples of vectors in that space, and a measurable map e : Sphere d × W → E, the row information is unchanged when e's value is appended to the side variable. Form the pushforward P' of P under ((s,w),G) ↦ ((s,(w,e(s,w))),G), so the side variable W becomes the pair (w, e(s,w)). Assume the Shannon entropy, ∫ −log π({v}) dπ(v) in the extended nonnegative reals, of the (W×E)-marginal π of P' is not infinite. Then rowInformation(P', gaussianRows m d) = rowInformation(P, gaussianRows m d), where rowInformation of a measure Q on ((S×W)×X) against γ on X is the Kullback-Leibler divergence of Q from the product of its (S×W)-marginal with γ, and gaussianRows m d is the product of m independent standard Gaussian measures on d-dimensional Euclidean space. The source gives this as an admitted theorem without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GaussianReplacement.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GaussianReplacement.lean; bytes 23277..23839
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GaussianReplacement

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InformationTheory

open scoped ENNReal NNReal RealInnerProductSpace Topology

noncomputable section

namespace CurrentProjection

theorem actualRowRefinement {d m : ℕ} {W E : Type*} [MeasurableSpace W]
    [MeasurableSpace E] [Countable W] [MeasurableSingletonClass W]
    [Countable E] [MeasurableSingletonClass E]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (e : Sphere d×W → E) (he : Measurable e)
    (_hEntropy : shannonEntropy
      ((P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))).map swapLast).snd ≠ ∞) :
    rowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) (gaussianRows m d) =
      rowInformation P (gaussianRows m d) := by
  sorry

end CurrentProjection
end
end OAI
