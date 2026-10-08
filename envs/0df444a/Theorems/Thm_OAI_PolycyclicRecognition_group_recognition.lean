-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_group_recognition
-- name    : OAI.PolycyclicRecognition.group_recognition
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:05.146274+00:00
-- url     : https://prove2.me/theorems/bbb1156e-2c0f-4b49-8072-a741df92aebd
-- statement:
--   The theorem states that, for finitely generated groups P and J (in Type) with a group coarse equivalence e from P to J, if P is virtually polycyclic then J is virtually polycyclic, and moreover there is a finite-index subgroup Γ of J together with a simply connected solvable Lie model S and a subgroup Λ of its underlying group such that Λ is a uniform lattice and Γ is isomorphic to Λ as a group. A group coarse equivalence consists of maps P→J and J→P, each bornologous in the sense that for every finite set S of differences x⁻¹y there is a finite set T of differences controlling (f x)⁻¹ f y, whose two composites differ from the identity by errors x⁻¹·invFun(toFun x) and y⁻¹·toFun(invFun y) ranging over finite sets. A group is virtually polycyclic if it has a finite-index subgroup admitting a finite chain of subgroups from the trivial subgroup to the whole subgroup, each normal in the next with cyclic quotient. A simply connected solvable Lie model is a finite-dimensional real normed space as model space, together with a smooth real Lie group structure on a Hausdorff, second countable, simply connected, solvable group. A uniform lattice Λ is a discrete subgroup admitting a compact set K such that every group element is a product γk with γ in Λ and k in K.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PolycyclicRecognition.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PolycyclicRecognition.lean; bytes 8041..8516
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

/-- Quasi-isometric recognition, including the finite-index uniform-lattice realization. -/
theorem group_recognition
    {P J : Type} [Group P] [Group J] [Group.FG P] [Group.FG J]
    (e : GroupCoarseEquivalence P J) (hP : IsVirtuallyPolycyclic P) :
    IsVirtuallyPolycyclic J ∧
      ∃ Γ : Subgroup J, Γ.FiniteIndex ∧
        ∃ (S : SimplyConnectedSolvableLieModel) (Λ : Subgroup S.carrier),
          IsUniformLattice Λ ∧ Nonempty (Γ ≃* Λ) := by
  sorry

end PolycyclicRecognition
end
end OAI
