-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_universal_fixed_kernel_impossible
-- name    : OAI.WeakPureInfiniteness.universal_fixed_kernel_impossible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:20:55.869552+00:00
-- url     : https://prove2.me/theorems/8cbf442a-07f8-4847-b72f-90e9a56cbaa6
-- title:
--   OAI.WeakPureInfiniteness.universal_fixed_kernel_impossible: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.universal_fixed_kernel_impossible` of [lean/OAI/Analysis/WeakInfiniteness/CrossUniverseKernelHeredity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/CrossUniverseKernelHeredity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open Filter Topology`, `open Complex selfAdjoint`, `open scoped ComplexOrder`, `open Filter Topology`):
--
--   ```lean
--   lemma universal_fixed_kernel_impossible
--       (h : ∀ z : MinimalTensor UniversalContraction (FullGroupAlgebra (FreeGroup Bool)),
--         minimalMapAny (NonUnitalStarAlgHom.id ℂ UniversalContraction)
--           fullToReducedLarge.toNonUnitalStarAlgHom z=0 →
--         z.val ∈ tensorKernelIdeal (A := UniversalContraction) fullToReducedLarge.toNonUnitalStarAlgHom) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.FullGroupAlgebra`, `OAI.WeakPureInfiniteness.UniversalContraction`, `OAI.WeakPureInfiniteness.instCStarAlgebraFullGroupAlgebra` and `OAI.WeakPureInfiniteness.instCStarAlgebraUniversalContraction` (definitions bundle `OAIQ246W000` of this split); `OAI.WeakPureInfiniteness.FreeTwo`, `OAI.WeakPureInfiniteness.GroupHilbert`, `OAI.WeakPureInfiniteness.uliftCStarAlgebra` and `OAI.WeakPureInfiniteness.uliftStarRing` (definitions bundle `OAIQ246W001` of this split); `OAI.WeakPureInfiniteness.ReducedFreeLarge`, `OAI.WeakPureInfiniteness.ReducedGroupAlgebra`, `OAI.WeakPureInfiniteness.fullToReducedLarge`, `OAI.WeakPureInfiniteness.instCStarAlgebraReducedGroupAlgebra`, `OAI.WeakPureInfiniteness.minimalMapAny` and `OAI.WeakPureInfiniteness.reducedGroupSubalgebra` (definitions bundle `OAIQ246W003` of this split); `OAI.WeakPureInfiniteness.MinimalTensor`, `OAI.WeakPureInfiniteness.SpatialAmbient`, `OAI.WeakPureInfiniteness.spatialAmbientCStar` and `OAI.WeakPureInfiniteness.tensorKernelIdeal` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proof of `OAI.WeakPureInfiniteness.exists_uniform_gap_any` of this split imports it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/CrossUniverseKernelHeredity.lean (declaration OAI.WeakPureInfiniteness.universal_fixed_kernel_impossible)

import Mathlib
import Definitions.Def_ExactInfiniteness
import Definitions.Def_OAIQ246W003

section

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
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open Filter Topology

universe u v w

lemma universal_fixed_kernel_impossible
    (h : ∀ z : MinimalTensor UniversalContraction (FullGroupAlgebra (FreeGroup Bool)),
      minimalMapAny (NonUnitalStarAlgHom.id ℂ UniversalContraction)
        fullToReducedLarge.toNonUnitalStarAlgHom z=0 →
      z.val ∈ tensorKernelIdeal (A := UniversalContraction) fullToReducedLarge.toNonUnitalStarAlgHom) : False := by
  sorry

end

end WeakPureInfiniteness
end

end OAI
end
