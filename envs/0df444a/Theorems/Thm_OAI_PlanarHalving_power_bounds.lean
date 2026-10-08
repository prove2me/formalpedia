-- Prove2me | Theorems.Thm_OAI_PlanarHalving_power_bounds
-- name    : OAI.PlanarHalving.power_bounds
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:04.534348+00:00
-- url     : https://prove2.me/theorems/c27843c1-9f1e-4321-92a9-c0a589cb257e
-- statement:
--   The theorem states that two power-saving bounds hold for planar point configurations P of n points, indexed by Fin n in ℝ². Let orient(p,q,r) be the signed area determinant (q₁−p₁)(r₂−p₂)−(q₂−p₂)(r₁−p₁). A configuration is in general position if P is injective and orient(P i,P j,P l)≠0 for all distinct i,j,l, so no three points are collinear. For such P, sideCount(i,j) is the number of points l with orient(P i,P j,P l)>0, and halvingCount(P) is the number of pairs i<j for which both sideCount(i,j) and sideCount(j,i) equal (n−2)/2, using natural-number division. First, there exist ε>0, a real C and a natural n₀ such that for every even n≥n₀ and every general-position P, halvingCount(P) ≤ C·n^(4/3−ε). Second, there exists ε>0 and a real C such that for every n≥1, every Generic P and every k≤n, switchCount(P,k) ≤ C·n^(4/3−ε). Generic means general position plus pairwise distinct x-coordinates, pairwise distinct slopes for distinct pairs i<j, and the condition that no point lying in the open segments of two distinct pairs lies in the closed segment of a third distinct pair. Here belowCount(i,j) counts points strictly below the line through P i and P j (in the sense that y−s·x is less than the value at P i, with s the slope), and switchCount(P,k) counts pairs i<j with 0<k<n and belowCount(i,j)=k−1. The proof is admitted in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HalvingLines.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HalvingLines.lean; bytes 1695..2168
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_HalvingLines

namespace OAI

namespace PlanarHalving

theorem power_bounds :
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, ∃ n₀ : ℕ,
      ∀ n : ℕ, Even n → n₀ ≤ n → ∀ P : Fin n → Point,
        GeneralPosition P → (halvingCount P : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε)) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ,
      ∀ n : ℕ, 1 ≤ n → ∀ P : Fin n → Point, Generic P →
        ∀ k : ℕ, k ≤ n → (switchCount P k : ℝ) ≤ C * (n : ℝ) ^ ((4 : ℝ) / 3 - ε)) :=
  sorry

end PlanarHalving
end OAI
