-- Prove2me | Theorems.Thm_OAI_WeakPureInfiniteness_exists_uniform_gap_any
-- name    : OAI.WeakPureInfiniteness.exists_uniform_gap_any
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T07:21:54.179208+00:00
-- url     : https://prove2.me/theorems/eefbe57c-c390-467d-b14d-434cd25a5573
-- title:
--   OAI.WeakPureInfiniteness.exists_uniform_gap_any: intermediate lemma from OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_individuallyProperlyInfinite_any` and `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Weak pure infiniteness and O-infinity absorption (result family 303)*, OpenAI Math Release, September 25, 2026, result family 303, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WeakPureInfiniteness.exists_uniform_gap_any` of [lean/OAI/Analysis/WeakInfiniteness/CrossUniverseUniformGap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/CrossUniverseUniformGap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WeakPureInfiniteness`, with `open scoped TensorProduct ENNReal ComplexOrder`, `open UniformSpace`, `open CStarAlgebra`, `open scoped NNReal`, `open scoped TensorProduct ComplexConjugate`, `open scoped ENNReal InnerProductSpace`, `open scoped InnerProductSpace`, `open scoped TensorProduct InnerProductSpace`, `open Filter Topology`, `open Complex selfAdjoint`, `open scoped ComplexOrder`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem exists_uniform_gap_any :
--       ∃ γ : ℝ, 0 < γ ∧ ∀ (B : Type u) [CStarAlgebra B] (v : B),
--         ‖v‖ ≤ 1 → Exact B → ¬ FiniteContractionModelsAny B v γ
--   ```
--
--   **Definitions.** The statement is written with `OAI.WeakPureInfiniteness.FiniteContractionModelsAny` (definitions bundle `OAIQ246W003` of this split); `OAI.WeakPureInfiniteness.Exact` (the published bundle `Def_ExactInfiniteness`).
--
--   **Used by.** The proofs of `OAI.WeakPureInfiniteness.exact_weaklyPurelyInfinite_stronglyPurelyInfinite` and `OAI.WeakPureInfiniteness.exists_binary_splitting_over_norm_slice_any` of this split import it.
-- source:
--   OpenAI, Weak pure infiniteness and O-infinity absorption (result family 303), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 303; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-pure-infiniteness-and-O-infinity-absorption-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/WeakInfiniteness/CrossUniverseUniformGap.lean (declaration OAI.WeakPureInfiniteness.exists_uniform_gap_any)

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

open Filter

open scoped Topology

universe u

theorem exists_uniform_gap_any :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (B : Type u) [CStarAlgebra B] (v : B),
      ‖v‖ ≤ 1 → Exact B → ¬ FiniteContractionModelsAny B v γ := by
  sorry

end

end WeakPureInfiniteness
end

end OAI
end
