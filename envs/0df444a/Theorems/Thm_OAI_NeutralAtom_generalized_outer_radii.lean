-- Prove2me | Theorems.Thm_OAI_NeutralAtom_generalized_outer_radii
-- name    : OAI.NeutralAtom.generalized_outer_radii
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:57.835119+00:00
-- url     : https://prove2.me/theorems/998b0c05-0582-48de-918f-df130d1d8410
-- statement:
--   The theorem states that, for every choice of wavefunctions Ψ_N for neutral atoms with N+1 electrons and nuclear charge Z=N+1 (each a spin-dependent complex function of N+1 positions in three-dimensional space, with spins taking two values), such that each Ψ_N is a normalized ground state, the outer radii of the atoms obey a Thomas–Fermi-type scaling law. A normalized ground state is an antisymmetric wavefunction with a weak gradient, square-integrable in each spin component together with its gradient, with finite Coulomb integrals against |Ψ|², total squared norm 1 summed over spins, and minimal energy among all such normalized functions. The energy is half the squared L² norm of the gradient plus the expectation of the Coulomb potential, which is −Z times the sum of inverse distances of electrons to the nucleus plus the sum of inverse inter-electron distances over pairs. The electron density is N+1 times the spin-summed integral of |Ψ|² over the other N positions, and the radius for m is the infimum of r≥0 such that the density mass outside the ball of radius r is at most m. For each m, upperRadius and lowerRadius are the limsup and liminf, in the extended reals, of these radii as N→∞ with N+1>m. With bTF=(81π²/2)^(1/3), the theorem states that both m^(1/3)·upperRadius(m) and m^(1/3)·lowerRadius(m) converge to bTF as m→∞ through the natural numbers.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoulombRadii.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoulombRadii.lean; bytes 3299..3709
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CoulombRadii

namespace OAI

noncomputable section

open MeasureTheory Filter

open scoped BigOperators Topology ContDiff

namespace NeutralAtom

theorem generalized_outer_radii
    (Ψ : ∀ N : ℕ, Wavefunction (N + 1))
    (hΨ : ∀ N : ℕ, IsNormalizedGroundState (N + 1) (Ψ N)) :
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * upperRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) ∧
    Tendsto (fun m : ℕ => (((m : ℝ) ^ (1 / 3 : ℝ) : ℝ) : EReal) * lowerRadius Ψ m)
      atTop (𝓝 (bTF : EReal)) := by
  sorry

end NeutralAtom
end
end OAI
