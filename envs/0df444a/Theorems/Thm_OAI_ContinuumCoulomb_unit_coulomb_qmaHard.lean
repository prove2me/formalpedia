-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_unit_coulomb_qmaHard
-- name    : OAI.ContinuumCoulomb.unit_coulomb_qmaHard
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:28.885695+00:00
-- url     : https://prove2.me/theorems/6079b0d2-224d-404a-b979-4fc8933c6fc9
-- statement:
--   The theorem states that the unit-charge continuum Coulomb ground-energy promise problem is QMA-hard under polynomial-time many-one reductions. An instance of UnitCoulomb is binary-encoded data consisting of a list of nuclei positions, each with three rational coordinates given as integer numerator and natural denominator, a unary-encoded number n of electrons, and rational bounds lower and upper. It is valid when there is at least one nucleus and one electron, all denominators are positive, the nuclear positions are pairwise distinct, and upper minus lower is at least 1. Every nucleus has charge exactly 1. For valid data, the energy form of an antisymmetric spin-valued state ψ with n electrons in three-dimensional space is its kinetic term, one half the sum of the squared L² norms of the weak gradient components, minus the nuclear attraction, the integral of the sum over electrons and nuclei of 1/|x_i − R_j| weighted by |ψ|², plus the electron-electron repulsion, the integral of the sum over pairs i<j of 1/|x_i − x_j| weighted by |ψ|². Here states are H¹ in each of n spin components with values in Fin 2, antisymmetric almost everywhere under simultaneous permutation of positions and spins up to the permutation sign. The ground energy is the infimum of this form over such states with total squared L² mass 1, valued in the extended reals. The yes instances are the valid ones whose ground energy is at most lower, and the no instances are the valid ones whose ground energy is at least upper. The theorem asserts that every promise problem in QMA, defined through polynomial-time uniformly generated quantum verifier circuits over Hadamard, T-phase and controlled-NOT gates, with acceptance probability at least 2/3 on some normalized witness for yes inputs and at most 1/3 on all normalized witnesses for no inputs, admits a polynomial-time computable map on bit strings sending yes instances to yes instances and no instances to no instances of this problem. In the source this theorem is admitted without proof.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ContinuumCoulombHardness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ContinuumCoulombHardness.lean; bytes 20468..20563
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_ContinuumCoulombHardness

namespace OAI

noncomputable section

open MeasureTheory

open scoped BigOperators

namespace ContinuumCoulomb

open BinaryEncoding Matrix

open scoped Kronecker

theorem unit_coulomb_qmaHard : QMAHard unitCoulombCodec.encode unitCoulombPromise := by
  sorry

end ContinuumCoulomb
end
end OAI
