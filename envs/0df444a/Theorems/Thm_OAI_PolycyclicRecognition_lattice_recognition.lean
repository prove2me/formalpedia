-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_lattice_recognition
-- name    : OAI.PolycyclicRecognition.lattice_recognition
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:05.289286+00:00
-- url     : https://prove2.me/theorems/c8f52373-1c44-4eec-9ff9-701b9b04f46f
-- statement:
--   The theorem states that, for any connected, simply connected, finite-dimensional real solvable Lie group G (a smooth second-countable Hausdorff Lie group, packaged as a model S) and any subgroup Λ of G that is a finite-covolume lattice, meaning Λ is discrete and the coset space G/Λ, with its Borel structure, carries a G-invariant probability measure, the following holds. If J is a finitely generated group and there is a coarse equivalence between Λ and J, meaning maps in both directions that send each finite set of left differences x⁻¹y into finite sets of left differences and whose composites differ from the identity by errors x⁻¹·g(f(x)) and y⁻¹·f(g(y)) ranging over finite sets, then J has a finite-index subgroup Γ for which there exist another connected, simply connected, finite-dimensional real solvable Lie group R and a uniform lattice Δ in R, that is, a discrete subgroup admitting a compact set K with every element of R equal to some γk with γ in Δ and k in K, such that Γ is isomorphic as a group to Δ. The ambient Lie group R is allowed to differ from G.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PolycyclicRecognition.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PolycyclicRecognition.lean; bytes 9563..10042
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PolycyclicRecognition

namespace OAI

noncomputable section

namespace PolycyclicRecognition

open Module LieAlgebra MeasureTheory

open scoped Manifold NNReal

attribute [instance] SimplyConnectedSolvableLieModel.normedAddCommGroup
  SimplyConnectedSolvableLieModel.normedSpace SimplyConnectedSolvableLieModel.finiteDimensional
  SimplyConnectedSolvableLieModel.topologicalSpace SimplyConnectedSolvableLieModel.chartedSpace
  SimplyConnectedSolvableLieModel.group SimplyConnectedSolvableLieModel.lieGroup
  SimplyConnectedSolvableLieModel.t2Space SimplyConnectedSolvableLieModel.simplyConnectedSpace
  SimplyConnectedSolvableLieModel.secondCountableTopology
  SimplyConnectedSolvableLieModel.solvable

/-- Finite-covolume lattice recognition, allowing a different ambient Lie group. -/
theorem lattice_recognition
    (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier)
    (hΛ : IsFiniteCovolumeLattice Λ)
    {J : Type} [Group J] [Group.FG J] (e : GroupCoarseEquivalence Λ J) :
    ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
      ∃ (R : SimplyConnectedSolvableLieModel) (Δ : Subgroup R.carrier),
        IsUniformLattice Δ ∧ Nonempty (Γ ≃* Δ) := by
  sorry

end PolycyclicRecognition
end
end OAI
