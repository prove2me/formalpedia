-- Prove2me | Theorems.Thm_OAI_RVM_datum_boundary_global_jets
-- name    : OAI.RVM.datum_boundary_global_jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:23:32.799588+00:00
-- url     : https://prove2.me/theorems/62dcc8a0-c2cf-4c98-a87e-ec251ad91988
-- title:
--   OAI.RVM.datum_boundary_global_jets: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.datum_boundary_global_jets` of [lean/OAI/Analysis/VlasovMaxwell/Retarded/MagneticBoundaryJets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/MagneticBoundaryJets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma datum_boundary_global_jets {d : Datum} (hd : Admissible d) (k : ℕ) :
--       ∃ C : ℝ, 0≤C ∧
--         (∀ x, ‖iteratedFDeriv ℝ k d.E₀ x‖≤C ∧ ‖iteratedFDeriv ℝ k d.B₀ x‖≤C) ∧
--         ∀ t∈Ioc (0:ℝ) 1,
--           (ContDiff ℝ ∞ (electricBoundaryField (datumBoundarySolution d) t) ∧
--             ContDiff ℝ ∞ (magneticBoundaryField (datumBoundarySolution d) t)) ∧
--           ∀ x, ‖iteratedFDeriv ℝ k (electricBoundaryField (datumBoundarySolution d) t) x‖≤C ∧
--             ‖iteratedFDeriv ℝ k (magneticBoundaryField (datumBoundarySolution d) t) x‖≤C
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.datumBoundarySolution`, `OAI.RVM.electricBoundaryField` and `OAI.RVM.magneticBoundaryField` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.uniform_picard_sequence_jets` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Retarded/MagneticBoundaryJets.lean (declaration OAI.RVM.datum_boundary_global_jets)

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma datum_boundary_global_jets {d : Datum} (hd : Admissible d) (k : ℕ) :
    ∃ C : ℝ, 0≤C ∧
      (∀ x, ‖iteratedFDeriv ℝ k d.E₀ x‖≤C ∧ ‖iteratedFDeriv ℝ k d.B₀ x‖≤C) ∧
      ∀ t∈Ioc (0:ℝ) 1,
        (ContDiff ℝ ∞ (electricBoundaryField (datumBoundarySolution d) t) ∧
          ContDiff ℝ ∞ (magneticBoundaryField (datumBoundarySolution d) t)) ∧
        ∀ x, ‖iteratedFDeriv ℝ k (electricBoundaryField (datumBoundarySolution d) t) x‖≤C ∧
          ‖iteratedFDeriv ℝ k (magneticBoundaryField (datumBoundarySolution d) t) x‖≤C := by
  sorry

end RVM
end

end OAI
end
