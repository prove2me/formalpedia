-- Prove2me | Theorems.Thm_OAI_Problem313_sharp_threshold_width
-- name    : OAI.Problem313.sharp_threshold_width
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:07.081791+00:00
-- url     : https://prove2.me/theorems/0a3ca649-f12e-4ff9-a506-fd9ade4ce1fc
-- statement:
--   The theorem states that, for every n ≥ 2, every Boolean function f on graph configurations on the vertex set Fin n, and every real ε with 0 < ε < 1/2, if f is vertex-invariant, increasing and nontrivial, then the width of its threshold window is at most (2^19 / (log n)^2) · log(1/(2ε)). Here a configuration assigns true or false to each two-element subset of Fin n, that is, it specifies which edges are present. f is vertex-invariant if f(permuteConfig π x) = f(x) for every permutation π of the vertices, where permuteConfig relabels the edges by π. f is increasing if, whenever x ≤ y (every edge present in x is present in y) and f(x) is true, f(y) is true. f is nontrivial if it takes the value true at some configuration and false at some configuration. For p in [0,1], graphMean p f is the sum over configurations x of f(x) (as 0 or 1) times the product-measure weight in which each edge is present independently with probability p, which is the probability that f is true. graphQuantile a f is the infimum of those p in [0,1] with graphMean p f ≥ a. The conclusion is that graphQuantile(1−ε, f) − graphQuantile(ε, f) ≤ (2^19 / (log n)^2) · log(1/(2ε)). The proof is admitted in the source, so this is stated, not verified.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SharpThreshold.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SharpThreshold.lean; bytes 1535..1913
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SharpThreshold

namespace OAI

noncomputable section

namespace Problem313

theorem sharp_threshold_width :
    ∀ (n : ℕ) (f : GraphConfig n → Bool) (ε : ℝ),
      2 ≤ n → VertexInvariant f → IncreasingGraphProperty f →
      NontrivialGraphProperty f → 0 < ε → ε < (1 / 2 : ℝ) →
      graphQuantile (1 - ε) f - graphQuantile ε f ≤
        ((2 : ℝ) ^ 19 / (Real.log (n : ℝ)) ^ 2) * Real.log (1 / (2 * ε)) := by
  sorry

end Problem313
end
end OAI
