-- Prove2me | Theorems.Thm_OAI_CoulombAtom_generalized_ionization
-- name    : OAI.CoulombAtom.generalized_ionization
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:29.871874+00:00
-- url     : https://prove2.me/theorems/db29ef9a-7631-4b32-8c96-e01d37a688c8
-- statement:
--   The theorem states that the proposition MainStatement holds: there is a real constant a>0 such that three asymptotic statements about atomic ionization energies all hold with this same a. Here the quantum energy of N electrons around a nucleus of charge Z is the infimum, taken over admissible spin-dependent wavefunctions on (ℝ³)^N, of the energy (1/2) times the total squared L² norm of all gradient components, minus Z times the expectation of Σᵢ 1/|xᵢ|, plus the expectation of Σ_{i<j} 1/|xᵢ−xⱼ|, with energy defined as 0 when N=0. Admissibility means that each spin component and each prescribed gradient component is square integrable, the gradient components are the weak partial derivatives of the values, the values are antisymmetric under simultaneous permutation of spins and positions (by the sign of the permutation, almost everywhere), the total squared norm summed over spins is 1, and the nuclear and electron-electron Coulomb densities are integrable. The ionization energy of removing m electrons from a neutral atom of charge Z is ionization(m,Z)=E(Z, Z−m)−E(Z, Z), with natural-number subtraction. The Thomas-Fermi energy tfEnergy(Z,M) is the infimum over nonnegative integrable densities ρ on ℝ³ of total mass M, with ρ^{5/3}, ρ/|x| and ρ(x)ρ(y)/|x−y| integrable, of (3/10)(3π²)^{2/3}∫ρ^{5/3} − Z∫ρ/|x| + (1/2)∬ρ(x)ρ(y)/|x−y|, and tfIonization(m,Z)=tfEnergy(Z,Z−m)−tfEnergy(Z,Z) for real m and Z. The three conclusions are: for every real m>0, tfIonization(m,Z) tends to a·m^{7/3} as the real number Z tends to infinity; for all natural-number sequences m_j, Z_j with 1≤m_j<Z_j, m_j→∞ and Z_j/m_j→∞, the ratio ionization(m_j,Z_j)/m_j^{7/3} tends to a; and as m→∞ through the naturals, both limsup and liminf over Z of ionization(m,Z), each divided by m^{7/3}, tend to a.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/CoulombIonization.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/CoulombIonization.lean; bytes 3519..3579
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_CoulombIonization

namespace OAI

open MeasureTheory Filter

open scoped Topology BigOperators ContDiff

noncomputable section

namespace CoulombAtom

theorem generalized_ionization : MainStatement := by
  sorry

end CoulombAtom
end
end OAI
