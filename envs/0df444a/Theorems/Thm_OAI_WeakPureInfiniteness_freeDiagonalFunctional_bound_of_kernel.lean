-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_freeDiagonalFunctional_bound_of_kernel
-- name    : OAI.WeakPureInfiniteness.freeDiagonalFunctional_bound_of_kernel
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:20:06.265921+00:00
-- url     : https://prove2.me/theorems/035e5c64-df3e-4b0c-a4a5-87fd9080d567
-- title:
--   OAI.WeakPureInfiniteness.freeDiagonalFunctional_bound_of_kernel: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.freeDiagonalFunctional_bound_of_kernel` of [lean/OAI/Analysis/WeakInfiniteness/NormKernelWitness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/NormKernelWitness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`):
--
--   ```lean
--   lemma freeDiagonalFunctional_bound_of_kernel
--       (hk : ∀ y : MinimalTensor (FullGroupAlgebra (FreeGroup Bool)) (FullGroupAlgebra (FreeGroup Bool)), minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom y = 0 →
--         freeDiagonalFunctional y = 0) :
--       ‖freeDiagonalFunctional freeDiagonalWitness‖ ≤ 2 * Real.sqrt 3
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.FullGroupAlgebra`, `OAI.WeakPureInfiniteness.instCStarAlgebraFullGroupAlgebra` and `OAI.WeakPureInfiniteness.minimalMapRight` (definitions bundle `OAIQ246W000` of this split); `OAI.WeakPureInfiniteness.FreeTwo`, `OAI.WeakPureInfiniteness.GroupHilbert`, `OAI.WeakPureInfiniteness.uliftCStarAlgebra` and `OAI.WeakPureInfiniteness.uliftStarRing` (definitions bundle `OAIQ246W001` of this split); `OAI.WeakPureInfiniteness.ReducedFreeLarge`, `OAI.WeakPureInfiniteness.ReducedGroupAlgebra`, `OAI.WeakPureInfiniteness.freeDiagonalFunctional`, `OAI.WeakPureInfiniteness.freeDiagonalWitness`, `OAI.WeakPureInfiniteness.fullToReducedLarge`, `OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra` and `OAI.WeakPureInfiniteness.reducedGroupSubalgebra` (definitions bundle `OAIQ246W003` of this split); `OAI.WeakPureInfiniteness.MinimalTensor`, `OAI.WeakPureInfiniteness.SpatialAmbient` and `OAI.WeakPureInfiniteness.spatialAmbientCStar` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proof of `OAI.WeakPureInfiniteness.universal_fixed_kernel_impossible` of this split imports it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/NormKernelWitness.lean (declaration OAI.WeakPureInfiniteness.freeDiagonalFunctional_bound_of_kernel)

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003

section

attribute [-instance] _root_.OAI.WeakPureInfiniteness.crossTensorGraphCStar _root_.OAI.WeakPureInfiniteness.instNonUnitalCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplexKernelAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

lemma freeDiagonalFunctional_bound_of_kernel
    (hk : ∀ y : MinimalTensor (FullGroupAlgebra (FreeGroup Bool)) (FullGroupAlgebra (FreeGroup Bool)), minimalMapRight (A := FullGroupAlgebra (FreeGroup Bool)) (C := FullGroupAlgebra (FreeGroup Bool)) (D := ReducedFreeLarge) fullToReducedLarge.toNonUnitalStarAlgHom y = 0 →
      freeDiagonalFunctional y = 0) :
    ‖freeDiagonalFunctional freeDiagonalWitness‖ ≤ 2 * Real.sqrt 3 := by
  sorry

end WeakPureInfiniteness
end

end OAI
end
