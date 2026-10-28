-- Prove2me | Theorems.Thm_OAI_RVM_transported_derivative_tame
-- name    : OAI.RVM.transported_derivative_tame
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:29:05.113014+00:00
-- url     : https://prove2.me/theorems/26e77336-a383-4c55-afc3-a01a9f015418
-- title:
--   OAI.RVM.transported_derivative_tame: intermediate lemma from OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RVM.global_classical_solution`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362)*, OpenAI Math Release, September 23, 2026, result family 362, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RVM.transported_derivative_tame` of [lean/OAI/Analysis/VlasovMaxwell/Geometry/ParticleTame.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Geometry/ParticleTame.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RVM`, with `open Set Filter Metric MeasureTheory`, `open scoped Topology ContDiff`):
--
--   ```lean
--   lemma transported_derivative_tame {d : Datum} (hd : Admissible d)
--       (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
--       ∃ C : ℝ, 0 ≤ C ∧ ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
--         ∀ (s : Solution), PicardRegular d s → TransportFor s E B →
--         ∀ T : ℝ, T∈Icc (0:ℝ) 1 → SpatialJetBound n T A E B →
--         ∀ H : ℝ, 0 ≤ H →
--         (∀ t∈Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ (n+1) (fun y => E (t,y)) x‖ ≤ H ∧
--           ‖iteratedFDeriv ℝ (n+1) (fun y => B (t,y)) x‖ ≤ H) →
--         ∀ t∈Icc 0 T, ∀ z, ‖iteratedFDeriv ℝ (n+1) (fun w => s.f (t,w)) z‖ ≤ C*(1+H)
--   ```
--
--   **Definitions.** The statement is written with `OAI.RVM.PicardRegular`, `OAI.RVM.SpatialJetBound` and `OAI.RVM.TransportFor` (definitions bundle `OAIQ073V000` of this split); `OAI.RVM.Admissible`, `OAI.RVM.Datum`, `OAI.RVM.Field`, `OAI.RVM.Phase`, `OAI.RVM.Solution` and `OAI.RVM.Vec` (the published bundle `Def_VlasovMaxwell`).
--
--   **Used by.** The proof of `OAI.RVM.uniform_picard_sequence_jets` of this split imports it.
-- source:
--   OpenAI, Global classical solutions of the three-dimensional relativistic Vlasov–Maxwell system (result family 362), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 362; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-classical-solutions-of-the-three-dimensional-relativistic-Vlasov-Maxwell-system-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/VlasovMaxwell/Geometry/ParticleTame.lean (declaration OAI.RVM.transported_derivative_tame)

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

lemma transported_derivative_tame {d : Datum} (hd : Admissible d)
    (n : ℕ) (hn : 1 ≤ n) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E B : Field), ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ (s : Solution), PicardRegular d s → TransportFor s E B →
      ∀ T : ℝ, T∈Icc (0:ℝ) 1 → SpatialJetBound n T A E B →
      ∀ H : ℝ, 0 ≤ H →
      (∀ t∈Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ (n+1) (fun y => E (t,y)) x‖ ≤ H ∧
        ‖iteratedFDeriv ℝ (n+1) (fun y => B (t,y)) x‖ ≤ H) →
      ∀ t∈Icc 0 T, ∀ z, ‖iteratedFDeriv ℝ (n+1) (fun w => s.f (t,w)) z‖ ≤ C*(1+H) := by
  sorry

end RVM
end

end OAI
end
