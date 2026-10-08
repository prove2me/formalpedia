-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_universal_energy_minimum
-- name    : OAI.AtomicTriangular.universal_energy_minimum
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:22.158256+00:00
-- url     : https://prove2.me/theorems/e25df6d0-a4c4-47db-8381-50ae96cdbc10
-- statement:
--   The theorem states that, for every function g: ℝ → ℝ that is smooth on (0, ∞), nonnegative there, and completely monotone in the sense that (−1)ʳg⁽ʳ⁾(t) ≥ 0 for every integer r ≥ 0 and t > 0, the density-one triangular lattice minimizes the following energy among all locally finite density-one subsets C of the Euclidean plane. Local finiteness means that C has finitely many points in every closed disk centered at the origin, and density one means that N_C(R)/(πR²) tends to 1 as R tends to infinity, where N_C(R) counts these points. The energy E_g(C) is the limit inferior, as R tends to infinity, of the sum of g(‖x − y‖²) over ordered distinct pairs of points in that disk, divided by N_C(R). These energies are evaluated in the extended nonnegative reals, allowing infinity. More precisely, put b = √3/2 and A = {b^(−1/2)(j + k/2, kb): j, k ∈ ℤ}. If L_g is the extended nonnegative sum of g(‖a‖²) over all nonzero a ∈ A, then L_g ≤ E_g(C) and L_g = E_g(A); thus the minimum is attained by A.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TriangularEnergy.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TriangularEnergy.lean; bytes 2143..2464
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_TriangularEnergy

namespace OAI

noncomputable section

open scoped BigOperators Topology ENNReal

open Classical Filter

namespace AtomicTriangular

/-- Universal energy minimality for smooth completely monotone potentials, with attainment. -/
theorem universal_energy_minimum (g : ℝ → ℝ) (C : Set Plane)
    (hg : AdmissiblePotential g) (hC : LocallyFinite C) (hd : DensityOne C) :
    latticeEnergy g ≤ energy g C ∧ latticeEnergy g = energy g A := by
  sorry

end AtomicTriangular
end
end OAI
