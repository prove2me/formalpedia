-- Prove2me | Theorems.Thm_OAI_YauCounterexamples_compact_profile_three_phase_data
-- name    : OAI.YauCounterexamples.compact_profile_three_phase_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T11:36:02.239037+00:00
-- url     : https://prove2.me/theorems/c28a92e2-dcba-4056-8d69-20fe5c1525ee
-- title:
--   OAI.YauCounterexamples.compact_profile_three_phase_data: intermediate lemma from OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.YauCounterexamples.sphere_three` and `OAI.YauCounterexamples.sphere_two_torus_two`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth counterexamples to Yau's nodal upper bound in dimensions three and four*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.YauCounterexamples.compact_profile_three_phase_data` of [lean/OAI/Geometry/SmoothYau/SphereMetric/CompactProfileThreePhaseData.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/CompactProfileThreePhaseData.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.YauCounterexamples`, with `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open MvPolynomial`, `open Set Filter`, `open scoped ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter Function MvPolynomial`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Function`, `open scoped Topology ContDiff`, `open Set Filter Matrix`, `open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem compact_profile_three_phase_data {X : Type*} [TopologicalSpace X] [CompactSpace X]
--       (H : X → RealForm PhaseSpace) (a : X → PhaseSpace)
--       (hH : Continuous (fun x => phaseFormMatrix (H x))) (ha : Continuous a)
--       (hsymm : ∀ x, (H x).IsSymm)
--       (hnc : ∀ x, a x ≠ 0 → ∃ b, inner ℝ (a x) b = 0 ∧ ‖b‖^2 = 1 + ‖a x‖^2 ∧
--         0 < H x (a x) (a x) + H x b b)
--       (hcrit : ∀ x, a x = 0 → ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
--         ∀ v ∈ P, v ≠ 0 → 0 < H x v v) :
--       ∃ δ₀ > 0, ∃ κ > 0, ∃ η > 0, ∃ C > 0, ∀ x ν,
--         ‖ν‖ = 1 → a x = ‖a x‖ • ν → ∀ δ ∈ Icc 0 δ₀,
--           ThreePhaseData (H x) (a x) ν δ κ η C
--   ```
--
--   **Definitions.** The statement is written with `OAI.YauCounterexamples.RealForm` (definitions bundle `OAIQ070A000` of this split); `OAI.YauCounterexamples.PhaseSpace` (definitions bundle `OAIQ070A002` of this split); `OAI.YauCounterexamples.ThreePhaseData` and `OAI.YauCounterexamples.phaseFormMatrix` (definitions bundle `OAIQ070A006` of this split).
--
--   **Used by.** The proofs of `OAI_YauCounterexamples_compact_profile_canonical_smallBall_uniform_orders` and `OAI.YauCounterexamples.normal_family_canonical_smallBall_uniform` of this split import it.
-- source:
--   OpenAI, Smooth counterexamples to Yau's nodal upper bound in dimensions three and four, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/Smooth-counterexamples-to-Yaus-nodal-upper-bound-in-dimensions-three-and-four-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/SmoothYau/SphereMetric/CompactProfileThreePhaseData.lean (declaration OAI.YauCounterexamples.compact_profile_three_phase_data)

import Mathlib
import Definitions.Def_OAIQ070A006

section

attribute [-instance] _root_.OAI.YauCounterexamples.circle_dimension_fact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace YauCounterexamples

open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Matrix
open scoped Topology InnerProductSpace Matrix Matrix.Norms.Elementwise

theorem compact_profile_three_phase_data {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : X → RealForm PhaseSpace) (a : X → PhaseSpace)
    (hH : Continuous (fun x => phaseFormMatrix (H x))) (ha : Continuous a)
    (hsymm : ∀ x, (H x).IsSymm)
    (hnc : ∀ x, a x ≠ 0 → ∃ b, inner ℝ (a x) b = 0 ∧ ‖b‖^2 = 1 + ‖a x‖^2 ∧
      0 < H x (a x) (a x) + H x b b)
    (hcrit : ∀ x, a x = 0 → ∃ P : Submodule ℝ PhaseSpace, Module.finrank ℝ P = 2 ∧
      ∀ v ∈ P, v ≠ 0 → 0 < H x v v) :
    ∃ δ₀ > 0, ∃ κ > 0, ∃ η > 0, ∃ C > 0, ∀ x ν,
      ‖ν‖ = 1 → a x = ‖a x‖ • ν → ∀ δ ∈ Icc 0 δ₀,
        ThreePhaseData (H x) (a x) ν δ κ η C := by
  sorry

end YauCounterexamples
end

end OAI
end
