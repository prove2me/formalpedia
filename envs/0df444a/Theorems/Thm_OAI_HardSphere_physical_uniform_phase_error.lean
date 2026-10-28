-- Prove2me | Theorems.Thm_OAI_HardSphere_physical_uniform_phase_error
-- name    : OAI.HardSphere.physical_uniform_phase_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:41:09.719466+00:00
-- url     : https://prove2.me/theorems/a300226a-cf18-4e1c-bc42-5b23b696618a
-- title:
--   OAI.HardSphere.physical_uniform_phase_error: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped ENNReal BigOperators Topology`):
--
--   ```lean
--   theorem physical_uniform_phase_error {A c : ℝ} (hA : 2≤A) (hc : 0 < c) :
--       ∃D₀ : ℝ,1≤D₀ ∧ ∃K₀ : ℕ,100≤K₀ ∧
--       ∀{N K : ℕ} [NeZero K] {L : Length},∀_hL : L.val=(K:ℝ),K₀≤K →
--       ∀D α : ℝ,D=(N+1:ℝ)/L.val^3 → D₀≤D → A/2≤α → α≤2*A →
--       ∀ψ : Jet (N+1) L,IsGroundVector (N+1) L (α/D) ψ →
--       Phase.modulusOccupation (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume-c/2≤
--         Phase.occupation (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.Phase.modulusOccupation` and `OAI.HardSphere.Phase.occupation` (definitions bundle `OAIQ054H001` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Direction`, `OAI.HardSphere.IsGroundVector`, `OAI.HardSphere.Jet`, `OAI.HardSphere.Length`, `OAI.HardSphere.ScalarL2`, `OAI.HardSphere.Torus` and `OAI.HardSphere.lengthPositive` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.condensation_with_mixed` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere
attribute [local instance] Classical.propDecidable

theorem physical_uniform_phase_error {A c : ℝ} (hA : 2≤A) (hc : 0 < c) :
    ∃D₀ : ℝ,1≤D₀ ∧ ∃K₀ : ℕ,100≤K₀ ∧
    ∀{N K : ℕ} [NeZero K] {L : Length},∀_hL : L.val=(K:ℝ),K₀≤K →
    ∀D α : ℝ,D=(N+1:ℝ)/L.val^3 → D₀≤D → A/2≤α → α≤2*A →
    ∀ψ : Jet (N+1) L,IsGroundVector (N+1) L (α/D) ψ →
    Phase.modulusOccupation (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume-c/2≤
      Phase.occupation (fun p : Configuration N L×Torus L ↦ ψ.1 (Fin.cons p.2 p.1)) volume volume := by
  sorry

end HardSphere
end
end

end OAI
end
