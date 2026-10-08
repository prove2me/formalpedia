-- Prove2me | Theorems.Thm_OAI_GeneralMahler_general_mahler
-- name    : OAI.GeneralMahler.general_mahler
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:42.382711+00:00
-- url     : https://prove2.me/theorems/ceafa7cb-36bb-46f2-9373-a620a64b4c29
-- statement:
--   In n-dimensional Euclidean space ℝⁿ, for a set K and a point z, polarAt(K,z) is the set of vectors y with ⟨y, x − z⟩ ≤ 1 for every x in K, the polar of K about the center z. The volumeProduct of K is the infimum, over all centers z in the interior of K, of vol(K)·vol(polarAt(K,z)), with volumes taken as real numbers (toReal of the Lebesgue measure). The theorem states that, for every dimension n ≥ 1 and every compact convex set K in ℝⁿ with nonempty interior, volumeProduct(K) ≥ (n+1)^(n+1)/(n!)². Moreover, volumeProduct(K) equals (n+1)^(n+1)/(n!)² exactly when K is a simplex, meaning that K is the convex hull of the range of some n+1 affinely independent points of ℝⁿ. The theorem is admitted in the source rather than proved there.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/GeneralMahler.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/GeneralMahler.lean; bytes 605..1204
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_GeneralMahler

namespace OAI

noncomputable section

open Set MeasureTheory

open scoped RealInnerProductSpace

namespace GeneralMahler

/-- The sharp general Mahler inequality, with equality exactly for simplices. -/
theorem general_mahler {n : ℕ} (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hcompact : IsCompact K) (hconvex : Convex ℝ K)
    (hinterior : (interior K).Nonempty) :
    ((n : ℝ) + 1) ^ (n + 1) / (Nat.factorial n : ℝ) ^ 2 ≤ volumeProduct K ∧
      (volumeProduct K = ((n : ℝ) + 1) ^ (n + 1) / (Nat.factorial n : ℝ) ^ 2 ↔
        ∃ vertices : Fin (n + 1) → EuclideanSpace ℝ (Fin n),
          AffineIndependent ℝ vertices ∧ K = convexHull ℝ (range vertices)) := by
  sorry

end GeneralMahler
end
end OAI
