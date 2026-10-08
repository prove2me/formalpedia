-- Prove2me | Theorems.Thm_OAI_ContinuumCoulomb_binary_coulomb_qmaHard
-- name    : OAI.ContinuumCoulomb.binary_coulomb_qmaHard
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:28.759176+00:00
-- url     : https://prove2.me/theorems/65228da5-6520-4cad-81ae-e0f0e42fde0b
-- statement:
--   The theorem states that the promise problem binaryCoulombPromise is QMA-hard under polynomial-time many-one reductions, with instances written using binaryCoulombCodec. QMA-hardness means that every promise problem P on bit strings lying in QMA, meaning it has a uniform polynomial-size quantum verifier circuit built from Hadamard, T-phase and controlled-NOT gates whose acceptance probability is at least 2/3 for some unit witness on yes instances and at most 1/3 for every unit witness on no instances, admits a polynomial-time computable map sending yes instances of P to yes instances of the Coulomb problem and no instances of P to no instances. An instance is a list of nuclei, each given by a position with three binary rational coordinates and a natural-number charge, together with a number of electrons (encoded in unary) and two binary rationals lower and upper. It is valid when there is at least one nucleus and one electron, all denominators are positive, the nuclear positions are distinct, every charge is positive, and upper minus lower is at least 1. A valid instance is a yes instance if the ground energy is at most lower and a no instance if it is at least upper. The ground energy is the infimum, in the extended reals, of the Coulomb energy form over antisymmetric spinful H¹ wavefunctions of the electrons in three dimensions with squared L² norm 1; the form is half the integrated squared gradient, minus the electron-nucleus attraction with weights charge/distance, plus the electron-electron repulsion 1/distance summed over pairs.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/ContinuumCoulombHardness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/ContinuumCoulombHardness.lean; bytes 20565..20666
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

theorem binary_coulomb_qmaHard : QMAHard binaryCoulombCodec.encode binaryCoulombPromise := by
  sorry

end ContinuumCoulomb
end
end OAI
