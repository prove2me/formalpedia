-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_positive_probability_transience_velocity_hemisphere
-- name    : OAI.DirectionalTransience.positive_probability_transience_velocity_hemisphere
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:35.272357+00:00
-- url     : https://prove2.me/theorems/1e056c90-1c8a-4fc8-bc62-c10293c89a2c
-- statement:
--   The theorem states the following for a dimension d≥3 and a probability measure ν on the set of transition rows, where a row is a nonnegative probability vector p indexed by the 2d nearest-neighbour directions ±e_i of the lattice ℤ^d. The environment assigns an independent ν-distributed row to every lattice site, and the walk, started at the origin, moves from its current site x in direction e with the probability that the row at x gives to e; the annealed law averages over environment and walk. Assume ν is uniformly elliptic, meaning that for some κ>0, ν-almost every row has every entry at least κ. Let ℓ be a nonzero real vector, and assume the annealed probability that the walk is transient in direction ℓ, i.e. that ⟨X_n,ℓ⟩ tends to +∞, is positive. Then there is a vector v, nonzero with ⟨v,ℓ⟩>0, such that the walk has asymptotic velocity v (X_n/n converges coordinatewise to v) with annealed probability 1, and v is the only vector with this property. Moreover, among unit vectors u, those with annealed probability 1 of transience in direction u coincide with those with positive such probability, and this set equals the open hemisphere of unit vectors u with ⟨v,u⟩>0. Finally, every unit vector u with ⟨v,u⟩≤0 has annealed probability 0 of transience in direction u. The statement is admitted without a proof in the source.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/VelocityHemisphere.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/VelocityHemisphere.lean; bytes 3394..4247
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_VelocityHemisphere

namespace OAI

open MeasureTheory ProbabilityTheory Filter

open scoped ENNReal NNReal BigOperators Topology

namespace DirectionalTransience

theorem positive_probability_transience_velocity_hemisphere
    {d : ℕ} (hd : 3 ≤ d) (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : ℓ ≠ 0)
    (hpos : 0 < annealedLaw ν (TransientPaths ℓ)) :
    ∃ v : Vector d,
      v ≠ 0 ∧ 0 < dot v ℓ ∧ annealedLaw ν (VelocityPaths v) = 1 ∧
      (∀ w : Vector d, annealedLaw ν (VelocityPaths w) = 1 → w = v) ∧
      {u : Vector d | dot u u = 1 ∧ annealedLaw ν (TransientPaths u) = 1} =
        {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} ∧
      {u : Vector d | dot u u = 1 ∧ 0 < annealedLaw ν (TransientPaths u)} =
        {u : Vector d | dot u u = 1 ∧ 0 < dot v u} ∧
      (∀ u : Vector d, dot u u = 1 → dot v u ≤ 0 →
        annealedLaw ν (TransientPaths u) = 0) := by
  sorry

end DirectionalTransience
end OAI
